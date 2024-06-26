//! Optimizations on MIR, including
//!
//! * Combining blocks

use std::collections::{BTreeMap, HashSet, VecDeque};

use get_many_mut::GetManyMutExt;
use itertools::Itertools;
use petgraph::graphmap::{DiGraphMap, GraphMap};

use crate::{
    ast::{ArithmeticOp, BinaryOp, ComparisonOp},
    hir::PointerSized,
};

use super::{
    BasicBlock, BasicBlockIdx, BasicOperation, Body, Constant, LocalOrConstant,
    Operand, Place, PlaceProjection, SlotIdx, Terminator, Value,
};

pub trait MirOptimization {
    /// Returns `true` if any changes occurred.
    fn apply(&self, body: &mut Body) -> bool;
}

/// MIR optimization that considers the control-flow graph of a `Body`, and
/// looks for pairs of blocks where:
/// * the "source block" has a `Goto` terminator going to the "destination
///   block"
/// * the "destination block"'s only source is the "source block"
///
/// Then, the "destination block"'s operations can be appended to the "source
/// block", and the "source block"'s terminator overwritten with the
/// "destination block"'s terminator.
///
/// Examples:
/// ```text
/// // Before:
/// bb0 {
///     op1;
///     op2;
///     goto -> bb1;
/// }
/// bb1 {
///     op3;
///     op4;
///     goto -> bb2;
/// }
/// // After:
/// bb0 {
///     op1;
///     op2;
///     op3;
///     op4;
///     goto -> bb2;
/// }
/// bb1 {
///     unreachable
/// }
/// ```
pub struct CombineBlocks;

impl MirOptimization for CombineBlocks {
    fn apply(&self, body: &mut Body) -> bool {
        enum BranchKind {
            Goto,
            /// A conditional branch, e.g. `SwitchBool`
            Conditional,
            Call,
        }

        let mut changed = false;

        let mut control_flow_graph: DiGraphMap<BasicBlockIdx, BranchKind> =
            GraphMap::with_capacity(
                body.basic_blocks.len(),
                body.basic_blocks.len(),
            );

        let add_edges_for_terminator =
            |control_flow_graph: &mut DiGraphMap<BasicBlockIdx, BranchKind>,
             src,
             terminator: &Terminator| {
                match *terminator {
                    Terminator::Goto { target } => {
                        control_flow_graph.add_edge(
                            src,
                            target,
                            BranchKind::Goto,
                        );
                    }
                    Terminator::SwitchBool { true_dst, false_dst, .. } => {
                        control_flow_graph.add_edge(
                            src,
                            true_dst,
                            BranchKind::Conditional,
                        );
                        control_flow_graph.add_edge(
                            src,
                            false_dst,
                            BranchKind::Conditional,
                        );
                    }
                    Terminator::SwitchCmp {
                        less_dst,
                        equal_dst,
                        greater_dst,
                        ..
                    } => {
                        control_flow_graph.add_edge(
                            src,
                            less_dst,
                            BranchKind::Conditional,
                        );
                        control_flow_graph.add_edge(
                            src,
                            equal_dst,
                            BranchKind::Conditional,
                        );
                        control_flow_graph.add_edge(
                            src,
                            greater_dst,
                            BranchKind::Conditional,
                        );
                    }
                    Terminator::Call { target, .. } => {
                        control_flow_graph.add_edge(
                            src,
                            target,
                            BranchKind::Call,
                        );
                    }
                    Terminator::Return | Terminator::Unreachable => {
                        // no edge to add
                    }
                    Terminator::Error => {
                        unreachable!(
                            "Terminator::Error encountered after MIR-building"
                        )
                    }
                }
            };

        for (src, block) in body.basic_blocks.iter().enumerate() {
            let src = BasicBlockIdx(src);
            control_flow_graph.add_node(src);
            add_edges_for_terminator(
                &mut control_flow_graph,
                src,
                &block.terminator,
            );
        }

        // For each block:
        // * If it has exactly one incoming neighbor,
        // * And that incoming edge is BranchKind::Goto,
        // * Then merge this block into the source, and update it's outgoing
        //   edges, if any, to start from the source
        for dst in 0..body.basic_blocks.len() {
            if let Ok((src, dst, BranchKind::Goto)) = control_flow_graph
                .edges_directed(
                    BasicBlockIdx(dst),
                    petgraph::Direction::Incoming,
                )
                .exactly_one()
            {
                if src == dst {
                    // cannot merge a block into itself
                    continue;
                }

                changed = true;

                // Merge dst into src
                #[allow(unstable_name_collisions)] // that's the point
                let [src_block, dst_block] =
                    body.basic_blocks.get_many_mut([src.0, dst.0]).unwrap();
                src_block.operations.append(&mut dst_block.operations);
                src_block.terminator = std::mem::replace(
                    &mut dst_block.terminator,
                    Terminator::Unreachable,
                );

                // Remove dst node, and then re-add edges from src
                control_flow_graph.remove_node(dst);
                add_edges_for_terminator(
                    &mut control_flow_graph,
                    src,
                    &src_block.terminator,
                );
            }
        }

        changed
    }
}

/// MIR optimization that removes blocks which are not reachable from any other
/// block.
///
/// Note that `bb0` will never be removed, as it is always considered reachable.
///
/// Examples:
/// ```text
/// // Before
/// bb0 {
///     goto -> bb1
/// }
/// bb1 {
///     op1;
///     goto -> bb3
/// }
/// bb2 {
///     op2;
///     goto -> bb3
/// }
/// bb3 {
///     return
/// }
/// // After
/// bb0 {
///     goto -> bb1
/// }
/// bb1 {
///     op1;
///     goto -> bb3
/// }
/// bb3 {
///     return
/// }
/// ```
pub struct TrimUnreachableBlocks;

fn find_reachable_blocks_from(
    body: &Body, from: impl IntoIterator<Item = BasicBlockIdx>,
) -> Vec<bool> {
    let from = from.into_iter();
    let mut reachable = vec![false; body.basic_blocks.len()];
    let mut frontier: VecDeque<BasicBlockIdx> =
        VecDeque::with_capacity(from.size_hint().0);

    macro_rules! insert_frontier {
        ($($block:expr),*) => {{
            $(
                let block = $block;
                if !reachable[block.0] {
                    reachable[block.0] = true;
                    frontier.push_back(block);
                }
            )*
        }};
    }

    for src in from {
        insert_frontier!(src);
    }

    while let Some(idx) = frontier.pop_front() {
        match body.basic_blocks[idx.0].terminator {
            Terminator::Goto { target } => {
                insert_frontier!(target);
            }
            Terminator::SwitchBool { true_dst, false_dst, .. } => {
                insert_frontier!(true_dst, false_dst);
            }
            Terminator::SwitchCmp {
                less_dst, equal_dst, greater_dst, ..
            } => {
                insert_frontier!(less_dst, equal_dst, greater_dst);
            }
            Terminator::Call { target, .. } => {
                insert_frontier!(target);
            }
            Terminator::Return | Terminator::Unreachable => {}
            Terminator::Error => unreachable!(),
        }
    }

    reachable
}

/// Used in TrimUnreachableBlocks and SortBlocks
///
/// `block_idx_mapping` should have a mapping from the old idx to the new idx
/// for every block which changed (i.e. if an entry is missing, it is assumed
/// that that block's index did not change).
fn fixup_terminators_after_changing_block_indices(
    blocks: &mut [BasicBlock], block_idx_mapping: &BTreeMap<usize, usize>,
) {
    macro_rules! fixup_block_idx {
        ($($block:expr),*) => {{
            $(
                let block: &mut BasicBlockIdx = $block;
                if let Some(&new) = block_idx_mapping.get(&block.0) {
                    block.0 = new;
                }
            )*
        }};
    }

    for block in blocks {
        match &mut block.terminator {
            Terminator::Goto { target } => fixup_block_idx!(target),
            Terminator::SwitchBool { true_dst, false_dst, .. } => {
                fixup_block_idx!(true_dst, false_dst)
            }
            Terminator::SwitchCmp {
                less_dst, equal_dst, greater_dst, ..
            } => {
                fixup_block_idx!(less_dst, equal_dst, greater_dst)
            }
            Terminator::Call { target, .. } => fixup_block_idx!(target),
            Terminator::Return | Terminator::Unreachable => {
                // no targets to fixup
            }
            Terminator::Error => {
                unreachable!("Terminator::Error after MIR-building")
            }
        }
    }
}

impl MirOptimization for TrimUnreachableBlocks {
    fn apply(&self, body: &mut Body) -> bool {
        let reachable = find_reachable_blocks_from(body, [BasicBlockIdx(0)]);

        // Now, we actually remove the now-unused blocks, then fixup all
        // terminators to point to the correct ones now.

        // Remove unused blocks
        let mut any_unreachable = false;
        for idx in (0..body.basic_blocks.len()).rev() {
            if !reachable[idx] {
                body.basic_blocks.remove(idx);
                any_unreachable = true;
            }
        }
        if !any_unreachable {
            // no blocks were unreachable, so nothing changes
            return false;
        }

        // Fixup the terminators of remaining blocks
        let block_idx_mapping: BTreeMap<usize, usize> = reachable
            .iter()
            .enumerate()
            .filter_map(|(idx, reachable)| reachable.then_some(idx))
            .zip(0..)
            .collect();

        fixup_terminators_after_changing_block_indices(
            &mut body.basic_blocks,
            &block_idx_mapping,
        );

        true
    }
}

/// Find slots which are only used in one body, are assigned from a Copy from
/// another slot or a constant, and are only used to be Copy'd from or in
/// `Switch` terminators, and try to inline them into their usage.
///
/// This is not always possible, e.g. if the slot they were copied from is
/// changed between the init and usage.
///
/// Note that this does *not* remove the original write to the slot. If it is
/// truly unused, it will be removed later by [`DeadLocalWriteElimination`].
///
/// TODO: expand this to handle the control-flow graph for inter-block
/// optimization, or maybe make a separate opt that does that.
///
/// Examples:
/// ```text
/// // Before
/// bb0 {
///     _3 = Copy(_2);
///     *_4 = Copy(_3);
///     _2 = Copy(_5);
///     *_6 = Copy(_3);
///     goto -> bb1;
/// }
/// // After
/// bb0 {
///     _3 = Copy(_2);
///     *_4 = Copy(_2);
///     _2 = Copy(_5);
///     *_6 = Copy(_3); // Note that this was not changed
///     goto -> bb1;
/// }
/// ```
/// ```text
/// // Before
/// bb0 {
///     _3 = const 5_i32;
///     *_4 = Copy(_3);
///     _5 = call(Copy(_3)) -> bb1;
/// }
/// // After
/// bb0 {
///     _3 = const 5_i32;
///     *_4 = const 5_i32;
///     _5 = call(const 5_i32) -> bb1;
/// }
/// ```
/// ```text
/// // Before
/// bb0 {
///     _2 = const 5_i32;
///     switchCmp(_2, _3) [less -> bb1, equal -> bb1, greater -> bb2]
/// }
/// // After
/// bb0 {
///     _2 = const 5_i32;
///     switchCmp(const 5_i32, _3) [less -> bb1, equal -> bb1, greater -> bb2]
/// }
/// ```
pub struct RedundantLocalReadEliminiation;

fn replace_copy_in_value(
    value: &mut Value, slot: SlotIdx, new_operand: &Operand,
) -> bool {
    match value {
        Value::Operand(operand) => {
            replace_copy_in_operand(operand, slot, new_operand)
        }
        Value::BinaryOp(_, lhs, rhs) => {
            let mut changed = false;
            changed |= replace_copy_in_operand(lhs, slot, new_operand);
            changed |= replace_copy_in_operand(rhs, slot, new_operand);
            changed
        }
        Value::Not(value) => replace_copy_in_value(value, slot, new_operand),
        Value::Negate(value) => replace_copy_in_value(value, slot, new_operand),
        Value::AddressOf(_, _place) => {
            eprintln!("TODO: replace copy in place addrof");
            false
        }
    }
}

fn replace_copy_in_operand(
    operand: &mut Operand, slot: SlotIdx, new_operand: &Operand,
) -> bool {
    match operand {
        // Replace the whole operand for a local place mention
        Operand::Copy(place)
            if place.local == slot && place.projection.is_none() =>
        {
            *operand = new_operand.clone();
            true
        }
        // Replace the index and the local in a projected place mention, if the
        // operand is a copy of a local.
        Operand::Copy(place) => {
            let Operand::Copy(new_operand) = new_operand else {
                return false;
            };
            if new_operand.projection.is_some() {
                return false;
            }
            let mut changed = false;
            if place.local == slot {
                place.local = new_operand.local;
            }
            if let Some(PlaceProjection::DerefIndex(index_slot)) =
                &mut place.projection
            {
                if *index_slot == slot && new_operand.projection.is_none() {
                    *index_slot = new_operand.local;
                    changed |= true;
                }
            }
            changed
        }
        Operand::Constant(..) => false,
    }
}

/// Replace `Copy(slot)` with `new_operand` anywhere it occurs. If this op is a
/// write to `src_local`, return a conflict. If this op is a write to a
/// deref-place, also replace `slot` in the place local and/or index.
///
/// Returns whether a change was made, and whether a conflict was detected.
fn replace_copy_in_operation(
    op: &mut BasicOperation, slot: SlotIdx, new_operand: &Operand,
    src_local: Option<SlotIdx>,
) -> (bool, bool) {
    match op {
        BasicOperation::Nop => (false, false),
        BasicOperation::Assign(place, value) => {
            let mut changed = replace_copy_in_value(value, slot, new_operand);
            let Some(projection) = &mut place.projection else {
                let conflict =
                    src_local.is_some_and(|src_local| src_local == place.local);
                return (changed, conflict);
            };
            let &Operand::Copy(Place {
                local: new_operand_local,
                projection: None,
            }) = new_operand
            else {
                return (changed, false);
            };

            if place.local == slot {
                place.local = new_operand_local;
                changed = true;
            }

            if let PlaceProjection::DerefIndex(index_slot) = projection {
                if *index_slot == slot {
                    *index_slot = new_operand_local;
                    changed = true;
                }
            }

            (changed, false)
        }
    }
}

fn replace_copy_in_switch_operand(
    operand: &mut LocalOrConstant, slot: SlotIdx, new_operand: &Operand,
) -> bool {
    let new_operand = match *new_operand {
        Operand::Copy(Place { local, projection: None }) => {
            LocalOrConstant::Local(local)
        }
        Operand::Copy(Place { projection: Some(..), .. }) => return false,
        Operand::Constant(ref constant) => {
            LocalOrConstant::Constant(constant.clone())
        }
    };
    let LocalOrConstant::Local(operand_slot) = operand else {
        return false;
    };
    if *operand_slot != slot {
        return false;
    }
    *operand = new_operand;
    true
}

impl MirOptimization for RedundantLocalReadEliminiation {
    fn apply(&self, body: &mut Body) -> bool {
        // TODO: expand this to look between basic blocks. For now it only works
        // in one basic block, which is probably good enough.

        let mut changed = false;

        for block in &mut body.basic_blocks {
            // For each operation, see if it is assigning a duplicable value to
            // a local slot. If so, replace that local in any
            // operations later in the block with the duplicable value, until it
            // becomes non-duplicable (e.g. because it is a Copy of a slot that
            // got written to).
            'this_block: for idx in 0..block.operations.len() {
                let BasicOperation::Assign(place, Value::Operand(operand)) =
                    &block.operations[idx]
                else {
                    continue;
                };
                if place.projection.is_some() {
                    // We only consider writes to locals directly.
                    // TODO: maybe consider writes to local array/tuple elements
                    // via index projections.
                    continue;
                }
                let slot = place.local;
                // Find the local being copied from in the assignment, so we can
                // stop if it changes, since that would make the optimization
                // incorrect.
                let src_local = match operand {
                    Operand::Copy(place) if place.projection.is_some() => {
                        // Conservatively don't deduplicate copies from more
                        // complicated places.
                        continue 'this_block;
                    }
                    Operand::Copy(place) => Some(place.local),
                    Operand::Constant(_) => None,
                };

                // Replace `Copy(slot)` with `new_operand` wherever it occurs in
                // the rest of the block.
                let new_operand = operand.clone();
                for op in &mut block.operations[idx + 1..] {
                    let (c, encountered_conflict) = replace_copy_in_operation(
                        op,
                        slot,
                        &new_operand,
                        src_local,
                    );
                    changed |= c;
                    if encountered_conflict {
                        continue 'this_block;
                    }
                }

                // Replace `Copy(slot)` with `new_operand` wherever it occurs in
                // the terminator, or replace `slot` with `new_operand` in
                // `Switch` terminators if it is `Copy(_)` or `const`.
                match &mut block.terminator {
                    Terminator::Call { func, args, .. } => {
                        changed |=
                            replace_copy_in_value(func, slot, &new_operand);
                        for arg in args {
                            changed |=
                                replace_copy_in_value(arg, slot, &new_operand);
                        }
                        // TODO: apply opt in place projections
                        #[cfg(any())]
                        {
                            changed |= replace_in_place_projections(
                                return_destination,
                                slot,
                                &new_operand,
                            );
                        }
                    }
                    Terminator::SwitchBool { scrutinee, .. } => {
                        changed |= replace_copy_in_switch_operand(
                            scrutinee,
                            slot,
                            &new_operand,
                        );
                    }
                    Terminator::SwitchCmp { lhs, rhs, .. } => {
                        changed |= replace_copy_in_switch_operand(
                            lhs,
                            slot,
                            &new_operand,
                        );
                        changed |= replace_copy_in_switch_operand(
                            rhs,
                            slot,
                            &new_operand,
                        );
                    }
                    Terminator::Goto { .. }
                    | Terminator::Return
                    | Terminator::Unreachable => {}
                    Terminator::Error => unreachable!(),
                }
            }
        }

        changed
    }
}

/// TODO: "dominate" is not the correct terminology here. I mean "this thing
/// *can* lead to the other thing", but "dominates" means "*every* path from the
/// start to the other thing goes through this thing". I can't think of the
/// correct terminology right now though, so 🤷.
///
/// Find assignments to locals which do not dominate in the control-flow-graph
/// any usages of that local before another write to that local, and
/// eliminate them.
///
/// Note that writes to `_0` which reach `return` are not dead, since `_0` is
/// the return slot.
///
/// Examples:
/// ```text
/// // Before
/// bb0 {
///     _0 = const 37; // Removed because it dominates _0 = const 21 below.
///     _3 = const 42; // Removed because _3 is not used after this
///     _0 = const 21;
///     return
/// }
/// // After
/// bb0 {
///     _0 = const 21; // Not removed because _0 is the return slot.
///     return
/// }
/// ```
/// ```text
/// // Before
/// bb0 {
///     _1 = const 37;
///     _2 = const 42;
///     goto -> bb1
/// }
/// bb1 {
///     _0 = Copy(_2);
///     return
/// }
/// // After
/// bb0 {
///     _2 = const 42;
///     goto -> bb1
/// }
/// bb1 {
///     _0 = Copy(_2);
///     return
/// }
/// ```
pub struct DeadLocalWriteElimination;

fn find_reads_in_value_read(slots: &mut [bool], value: &Value) {
    match value {
        Value::Operand(operand) => find_reads_in_operand_read(slots, operand),
        Value::BinaryOp(_, lhs, rhs) => {
            find_reads_in_operand_read(slots, lhs);
            find_reads_in_operand_read(slots, rhs);
        }
        Value::Not(value) => find_reads_in_value_read(slots, value),
        Value::Negate(value) => find_reads_in_value_read(slots, value),
        Value::AddressOf(_, place) => {
            find_reads_in_place_evaluation(slots, place)
        }
    }
}

/// For each slot that is read when this `Operand` is evaluated in a
/// `Value::Operand`, set the corresponding element of `slots` to `true`.
fn find_reads_in_operand_read(slots: &mut [bool], operand: &Operand) {
    match operand {
        Operand::Copy(place) => find_reads_in_place_read(slots, place),
        Operand::Constant(..) => {}
    }
}

/// For each slot that is read when this `Place` is evaluated, but not read or
/// written (e.g. in an `Value::AddressOf`), set the corresponding element of
/// `slots` to `true`.
fn find_reads_in_place_evaluation(slots: &mut [bool], place: &Place) {
    if let Some(projection) = &place.projection {
        // If this is a deref place, then it's not actually
        // writing to the place's local, it's *reading* it.
        slots[place.local.0] = true;
        match projection {
            PlaceProjection::DerefIndex(index_slot) => {
                slots[index_slot.0] = true;
            }
            PlaceProjection::DerefConstantIndex(_) | PlaceProjection::Deref => {
            }
        }
    }
}

/// For each slot that is read when this `Place` is evaluated in a
/// `Value::Operand(Operand::Place(..))`, set the corresponding element of
/// `slots` to `true`.
fn find_reads_in_place_read(slots: &mut [bool], place: &Place) {
    find_reads_in_place_evaluation(slots, place);
    slots[place.local.0] = true;
}

/// For each slot that is read when this `Place` is evaluated as the assignee,
/// set the corresponding element of `slots` to `true`.
fn find_reads_in_place_write(slots: &mut [bool], place: &Place) {
    find_reads_in_place_evaluation(slots, place);
}

impl MirOptimization for DeadLocalWriteElimination {
    fn apply(&self, body: &mut Body) -> bool {
        // TODO: Currently this conservatively only removes writes to locals
        // which are *never* used (not just that aren't used before the local is
        // written to again), because that is easier to implement.

        // Find all locals which are *ever* read from.
        let mut slots = vec![false; body.slots.len()];

        for block in &body.basic_blocks {
            for op in &block.operations {
                match op {
                    BasicOperation::Nop => {}
                    BasicOperation::Assign(place, value) => {
                        find_reads_in_place_write(&mut slots, place);
                        find_reads_in_value_read(&mut slots, value);
                    }
                }
            }
            match &block.terminator {
                Terminator::SwitchBool { scrutinee, .. } => {
                    if let LocalOrConstant::Local(scrutinee) = scrutinee {
                        slots[scrutinee.0] = true;
                    }
                }
                Terminator::SwitchCmp { lhs, rhs, .. } => {
                    if let LocalOrConstant::Local(lhs) = lhs {
                        slots[lhs.0] = true;
                    }
                    if let LocalOrConstant::Local(rhs) = rhs {
                        slots[rhs.0] = true;
                    }
                }
                Terminator::Return => {
                    // If we reach a return, then `_0` is read.
                    slots[0] = true;
                }
                Terminator::Goto { .. } | Terminator::Unreachable => {}
                Terminator::Call { func, args, return_destination, .. } => {
                    find_reads_in_value_read(&mut slots, func);
                    for arg in args {
                        find_reads_in_value_read(&mut slots, arg);
                    }
                    find_reads_in_place_write(&mut slots, return_destination);
                }
                Terminator::Error => unreachable!(),
            }
        }

        // Now, go through and remove all writes to slots which are never read.
        // Note: we don't remove `Call`s which write to these slots, since they
        // can have side effects.
        let mut any_removed = false;
        for block in &mut body.basic_blocks {
            block.operations.retain(|op| match op {
                BasicOperation::Nop => true,
                BasicOperation::Assign(place, _) => {
                    let should_remove =
                        place.projection.is_none() && !slots[place.local.0];
                    any_removed |= should_remove;
                    !should_remove
                }
            });
        }

        any_removed
    }
}

/// MIR optimization that removes slots which are not read or written in any
/// block.
///
/// Note that `_0` (the return slot) and argument slots will never be removed.
///
/// Examples:
/// ```text
/// // Before
/// bb0 {
///     goto -> bb1
/// }
/// bb1 {
///     op1;
///     goto -> bb3
/// }
/// bb2 {
///     op2;
///     goto -> bb3
/// }
/// bb3 {
///     return
/// }
/// // After
/// bb0 {
///     goto -> bb1
/// }
/// bb1 {
///     op1;
///     goto -> bb3
/// }
/// bb3 {
///     return
/// }
/// ```
pub struct TrimUnusedSlots;

fn find_slot_uses_in_value(slots: &mut [bool], value: &Value) {
    match value {
        Value::Operand(operand) => {
            find_slot_uses_in_operand(slots, operand);
        }
        Value::BinaryOp(_, lhs, rhs) => {
            find_slot_uses_in_operand(slots, lhs);
            find_slot_uses_in_operand(slots, rhs);
        }
        Value::Not(value) | Value::Negate(value) => {
            find_slot_uses_in_value(slots, value)
        }
        Value::AddressOf(_, place) => find_slot_uses_in_place(slots, place),
    }
}

fn find_slot_uses_in_operand(slots: &mut [bool], operand: &Operand) {
    match operand {
        Operand::Constant(..) => {}
        Operand::Copy(place) => find_slot_uses_in_place(slots, place),
    }
}

fn find_slot_uses_in_place(slots: &mut [bool], place: &Place) {
    slots[place.local.0] = true;
    if let Some(PlaceProjection::DerefIndex(slot)) = place.projection {
        slots[slot.0] = true
    }
}

fn find_slot_uses_in_basic_block(slots: &mut [bool], block: &BasicBlock) {
    for op in &block.operations {
        find_slot_uses_in_basic_operation(slots, op);
    }

    find_slot_uses_in_terminator(slots, &block.terminator);
}

fn find_slot_uses_in_basic_operation(slots: &mut [bool], op: &BasicOperation) {
    match op {
        BasicOperation::Nop => {}
        BasicOperation::Assign(place, value) => {
            find_slot_uses_in_place(slots, place);
            find_slot_uses_in_value(slots, value);
        }
    }
}

fn find_slot_uses_in_terminator(slots: &mut [bool], terminator: &Terminator) {
    match terminator {
        Terminator::SwitchBool { scrutinee, .. } => {
            if let LocalOrConstant::Local(scrutinee) = scrutinee {
                slots[scrutinee.0] = true;
            }
        }
        Terminator::SwitchCmp { lhs, rhs, .. } => {
            if let LocalOrConstant::Local(lhs) = lhs {
                slots[lhs.0] = true;
            }
            if let LocalOrConstant::Local(rhs) = rhs {
                slots[rhs.0] = true;
            }
        }
        Terminator::Goto { .. }
        | Terminator::Return
        | Terminator::Unreachable => {}
        Terminator::Call { func, args, return_destination, .. } => {
            find_slot_uses_in_value(slots, func);
            for arg in args {
                find_slot_uses_in_value(slots, arg);
            }
            find_slot_uses_in_place(slots, return_destination);
        }
        Terminator::Error => unreachable!(),
    }
}

fn replace_slot(
    slots: &BTreeMap<SlotIdx, SlotIdx>, slot: &mut SlotIdx,
) -> bool {
    match slots.get(slot) {
        // Don't replace if it's already the same
        Some(new_slot) if *new_slot == *slot => false,
        Some(new_slot) => {
            *slot = *new_slot;
            true
        }
        None => false,
    }
}

fn replace_slot_uses_in_value(
    slots: &BTreeMap<SlotIdx, SlotIdx>, value: &mut Value,
) -> bool {
    match value {
        Value::Operand(operand) => replace_slot_uses_in_operand(slots, operand),
        Value::BinaryOp(_, lhs, rhs) => {
            let mut changed = false;
            changed |= replace_slot_uses_in_operand(slots, lhs);
            changed |= replace_slot_uses_in_operand(slots, rhs);
            changed
        }
        Value::Not(value) | Value::Negate(value) => {
            replace_slot_uses_in_value(slots, value)
        }
        Value::AddressOf(_, place) => replace_slot_uses_in_place(slots, place),
    }
}

fn replace_slot_uses_in_operand(
    slots: &BTreeMap<SlotIdx, SlotIdx>, operand: &mut Operand,
) -> bool {
    match operand {
        Operand::Constant(_) => false,
        Operand::Copy(place) => replace_slot_uses_in_place(slots, place),
    }
}

fn replace_slot_uses_in_place(
    slots: &BTreeMap<SlotIdx, SlotIdx>, place: &mut Place,
) -> bool {
    let mut changed = replace_slot(slots, &mut place.local);
    if let Some(PlaceProjection::DerefIndex(slot)) = &mut place.projection {
        changed |= replace_slot(slots, slot);
    }
    changed
}

fn replace_slot_uses_in_basic_block(
    slots: &BTreeMap<SlotIdx, SlotIdx>, block: &mut BasicBlock,
) -> bool {
    let mut changed = false;

    for op in &mut block.operations {
        changed |= replace_slot_uses_in_basic_operation(slots, op);
    }

    changed |= replace_slot_uses_in_terminator(slots, &mut block.terminator);

    changed
}

fn replace_slot_uses_in_basic_operation(
    slots: &BTreeMap<SlotIdx, SlotIdx>, op: &mut BasicOperation,
) -> bool {
    match op {
        BasicOperation::Nop => false,
        BasicOperation::Assign(place, value) => {
            let mut changed = false;
            changed |= replace_slot_uses_in_place(slots, place);
            changed |= replace_slot_uses_in_value(slots, value);
            changed
        }
    }
}

fn replace_slot_uses_in_terminator(
    slots: &BTreeMap<SlotIdx, SlotIdx>, terminator: &mut Terminator,
) -> bool {
    match terminator {
        Terminator::Goto { .. }
        | Terminator::Unreachable
        | Terminator::Return => false,
        Terminator::SwitchBool { scrutinee, .. } => {
            if let LocalOrConstant::Local(scrutinee) = scrutinee {
                replace_slot(slots, scrutinee)
            } else {
                false
            }
        }
        Terminator::SwitchCmp { lhs, rhs, .. } => {
            let mut changed = false;
            if let LocalOrConstant::Local(lhs) = lhs {
                changed |= replace_slot(slots, lhs);
            }
            if let LocalOrConstant::Local(rhs) = rhs {
                changed |= replace_slot(slots, rhs);
            }
            changed
        }
        Terminator::Call { func, args, return_destination, .. } => {
            let mut changed = false;
            changed |= replace_slot_uses_in_value(slots, func);

            for arg in args {
                changed |= replace_slot_uses_in_value(slots, arg);
            }

            changed |= replace_slot_uses_in_place(slots, return_destination);

            changed
        }
        Terminator::Error => unreachable!(),
    }
}

impl MirOptimization for TrimUnusedSlots {
    fn apply(&self, body: &mut Body) -> bool {
        let mut slots = vec![false; body.slots.len()];
        // Return slot and argument slots are always considered used
        slots[..=body.argc].fill(true);

        // Find all slot uses
        for block in &body.basic_blocks {
            find_slot_uses_in_basic_block(&mut slots, block);
        }

        if slots.iter().all(|&used| used) {
            // All slots are used, no changed
            return false;
        }

        // Remove unused slots
        let mut iter = slots.iter().copied();
        body.slots.retain(|_| iter.next().unwrap_or(true));

        // Replace slots with their new values
        let slot_idx_mapping: BTreeMap<SlotIdx, SlotIdx> = slots
            .iter()
            .enumerate()
            .filter_map(|(idx, used)| used.then_some(SlotIdx(idx)))
            .zip((0..).map(SlotIdx))
            .collect();

        for block in &mut body.basic_blocks {
            replace_slot_uses_in_basic_block(&slot_idx_mapping, block);
        }

        true
    }
}

/// MIR optimization that propagates constant values in operations.
///
/// Examples:
/// ```text
/// // Before:
/// bb0 {
///     _0 = Add(Copy(_1), const 0);
///     return
/// }
/// // After
/// bb0 {
///     _0 = Copy(_1);
///     return
/// }
/// ```
/// ```text
/// // Before:
/// bb0 {
///     _0 = Add(const 2, const 3);
///     return
/// }
/// // After
/// bb0 {
///     _0 = const 5;
///     return
/// }
/// ```
pub struct ConstantPropagation;

fn constant_propagate_value(value: &mut Value) -> bool {
    macro_rules! make_ops {
        ($($op:pat => $($u128_method:ident)? $(|$lhs:ident, $rhs:ident| $value:expr)?;)*) => {
            match value {
                $(
                    &mut Value::BinaryOp(
                        $op,
                        Operand::Constant(Constant::Integer { value: lhs, signed: lhs_signed, bits: lhs_bits }),
                        Operand::Constant(Constant::Integer { value: rhs, signed: rhs_signed, bits: rhs_bits }),
                    ) => {
                        if lhs_signed != rhs_signed || lhs_bits != rhs_bits {
                            dbg!(lhs_signed, rhs_signed, lhs_bits, rhs_bits);
                            panic!("operating on different-typed integers");
                        }
                        $(
                            *value = Value::Operand(Operand::Constant(Constant::Integer {
                                value: u128::$u128_method(lhs, rhs),
                                signed: lhs_signed,
                                bits: lhs_bits,
                            }));
                        )?
                        $(
                            *value = Value::Operand(Operand::Constant(Constant::Integer {
                                value: {
                                    let $lhs = lhs;
                                    let $rhs = rhs;
                                    $value
                                },
                                signed: lhs_signed,
                                bits: lhs_bits,
                            }));
                        )?
                        true
                    },
                )*
                // x + 0 or x - 0 or 0 + x => x
                Value::BinaryOp(
                    BinaryOp::Arithmetic(ArithmeticOp::Add) | BinaryOp::Arithmetic(ArithmeticOp::Subtract),
                    other,
                    Operand::Constant(Constant::Integer{ value: 0, .. }),
                ) | Value::BinaryOp(
                    BinaryOp::Arithmetic(ArithmeticOp::Add),
                    Operand::Constant(Constant::Integer{ value: 0, .. }),
                    other,
                ) => {
                    *value = Value::Operand(other.clone());
                    true
                }
                Value::Operand(_) => false,
                Value::BinaryOp(_, _, _) => false,
                Value::AddressOf(_, _) => false,
                Value::Negate(inner) => {
                    let inner_changed = constant_propagate_value(inner);
                    match **inner {
                        // -constant -> constant
                        Value::Operand(Operand::Constant(Constant::Integer { value: inner, signed, bits })) => {
                            *value = Value::from(Constant::Integer{ value: u128::wrapping_neg(inner), signed, bits });
                            true
                        }
                        // --value -> value
                        Value::Negate(ref inner) => {
                            match **inner {
                                Value::Negate(ref inner) => {
                                    *value = (**inner).clone();
                                    true
                                }
                                _ => inner_changed,
                            }
                        }
                        _ => inner_changed
                    }
                }
                Value::Not(inner) => {
                    let inner_changed = constant_propagate_value(inner);
                    match **inner {
                        // -constant -> constant
                        Value::Operand(Operand::Constant(Constant::Integer { value: inner, signed, bits })) => {
                            *value = Value::from(Constant::Integer{ value: !inner, signed, bits });
                            true
                        }
                        // -constant -> constant
                        Value::Operand(Operand::Constant(Constant::Bool(inner))) => {
                            *value = Value::from(Constant::Bool(!inner));
                            true
                        }
                        // !!value -> value
                        Value::Not(ref inner) => {
                            match **inner {
                                Value::Not(ref inner) => {
                                    *value = (**inner).clone();
                                    true
                                }
                                _ => inner_changed,
                            }
                        }
                        _ => inner_changed
                    }
                }
            }
        };
    }
    make_ops! {
        BinaryOp::Arithmetic(ArithmeticOp::Add) => wrapping_add;
        BinaryOp::Arithmetic(ArithmeticOp::Subtract) => wrapping_sub;
        BinaryOp::Arithmetic(ArithmeticOp::Multiply) => wrapping_mul;
        // TODO: division and modulo require knowing signedness
        // BinaryOp::Arithmetic(ArithmeticOp::Divide) => |lhs, rhs| match u128::checked_div(lhs, rhs) {
        //     Some(value) => value,
        //     None => return false, // Don't attempt to optimize divisions by zero
        // };
        // BinaryOp::Arithmetic(ArithmeticOp::Modulo) => |lhs, rhs| match u128::checked_mod(lhs, rhs) {
        //     Some(value) => value,
        //     None => return false, // Don't attempt to optimize divisions by zero
        // };
    }
}

impl MirOptimization for ConstantPropagation {
    fn apply(&self, body: &mut Body) -> bool {
        let mut changed = false;
        for block in &mut body.basic_blocks {
            for op in &mut block.operations {
                match op {
                    BasicOperation::Nop => {}
                    BasicOperation::Assign(_place, value) => {
                        changed |= constant_propagate_value(value);
                    }
                }
            }
        }
        changed
    }
}

/// Reduce a BinaryOp comparison assignment to a local followed immediately by a
/// switchBool terminator on that local to an equvalent switchCmp terminator.
///
/// Note: Does not remove the comparison op/assignment, as the local may be used
/// later.
///
/// Example:
/// ```text
/// // Before
/// bb0 {
///     _1 = LessEq(Copy(_3), Copy(_4));
///     switchBool(_1) [false -> bb1, true -> bb2]
/// }
/// // After
/// bb0 {
///     _1 = LessEq(_3, _4);
///     switchCmp(_3, _4) [Less -> bb2, Equal -> bb2, Greater -> bb1]
/// }
/// ```
pub struct InsertSwitchCompare;

impl MirOptimization for InsertSwitchCompare {
    fn apply(&self, body: &mut Body) -> bool {
        let mut changed = false;
        for block in &mut body.basic_blocks {
            let Terminator::SwitchBool {
                scrutinee: LocalOrConstant::Local(scrutinee),
                true_dst,
                false_dst,
            } = block.terminator
            else {
                continue;
            };
            let Some(BasicOperation::Assign(place, value)) =
                block.operations.last()
            else {
                continue;
            };
            if place.local != scrutinee || place.projection.is_some() {
                continue;
            }
            let Value::BinaryOp(BinaryOp::Comparison(cmp_op), lhs, rhs) = value
            else {
                continue;
            };
            let lhs = match lhs {
                &Operand::Copy(Place { local, projection: None }) => {
                    LocalOrConstant::Local(local)
                }
                Operand::Constant(constant) => {
                    LocalOrConstant::Constant(constant.clone())
                }
                _ => continue,
            };
            let rhs = match rhs {
                &Operand::Copy(Place { local, projection: None }) => {
                    LocalOrConstant::Local(local)
                }
                Operand::Constant(constant) => {
                    LocalOrConstant::Constant(constant.clone())
                }
                _ => continue,
            };
            let (less_dst, equal_dst, greater_dst) = match cmp_op {
                ComparisonOp::Equal => (false_dst, true_dst, false_dst),
                ComparisonOp::NotEqual => (true_dst, false_dst, true_dst),
                ComparisonOp::Less => (true_dst, false_dst, false_dst),
                ComparisonOp::Greater => (false_dst, false_dst, true_dst),
                ComparisonOp::LessEq => (true_dst, true_dst, false_dst),
                ComparisonOp::GreaterEq => (false_dst, true_dst, true_dst),
            };
            block.terminator = Terminator::SwitchCmp {
                lhs,
                rhs,
                less_dst,
                equal_dst,
                greater_dst,
            };
            changed = true;
        }
        changed
    }
}

/// Find `SwtichBool` and `SwitchCmp` terminators with only a single target, or
/// whose condition is known, and replace them with `Goto` terminators.
///
/// Examples:
/// ```text
/// // Before
/// bb0 {
///     _1 = And(_3, _4);
///     switchBool(_1) [false -> bb1, true -> bb1]
/// }
/// // After
/// bb0 {
///     _1 = And(_3, _4);
///     goto -> bb1
/// }
/// ```
/// ```text
/// // Before
/// bb0 {
///     switchBool(const true) [false -> bb1, true -> bb2]
/// }
/// // After
/// bb0 {
///     goto -> bb2
/// }
/// ```
pub struct RedundantSwitchElimination;

impl MirOptimization for RedundantSwitchElimination {
    fn apply(&self, body: &mut Body) -> bool {
        let mut changed = false;
        for block in &mut body.basic_blocks {
            match block.terminator {
                Terminator::SwitchBool {
                    ref scrutinee,
                    true_dst,
                    false_dst,
                } => {
                    if true_dst == false_dst {
                        block.terminator =
                            Terminator::Goto { target: true_dst };
                        changed = true;
                    } else if let LocalOrConstant::Constant(scrutinee) =
                        scrutinee
                    {
                        let next_bb = match scrutinee {
                            Constant::Bool(true) => true_dst,
                            Constant::Bool(false) => false_dst,
                            _ => unreachable!(
                                "non-bool constant in switchBool scrutinee"
                            ),
                        };
                        block.terminator = Terminator::Goto { target: next_bb };
                        changed = true;
                    }
                }
                Terminator::SwitchCmp {
                    ref lhs,
                    ref rhs,
                    less_dst,
                    equal_dst,
                    greater_dst,
                } => {
                    if less_dst == equal_dst && equal_dst == greater_dst {
                        block.terminator =
                            Terminator::Goto { target: less_dst };
                        changed = true;
                    } else if let (
                        LocalOrConstant::Constant(lhs),
                        LocalOrConstant::Constant(rhs),
                    ) = (lhs, rhs)
                    {
                        let Constant::Integer {
                            value: lhs,
                            signed: lhs_signed,
                            bits: lhs_bits,
                        } = *lhs
                        else {
                            unreachable!("non-integer in switchCmp terminator")
                        };
                        let Constant::Integer {
                            value: rhs,
                            signed: rhs_signed,
                            bits: rhs_bits,
                        } = *rhs
                        else {
                            unreachable!("non-integer in switchCmp terminator")
                        };
                        if lhs_signed != rhs_signed || lhs_bits != rhs_bits {
                            unreachable!(
                                "comparing different-typed integers in \
                                 SwitchCmp terminator"
                            );
                        }
                        let bits = match lhs_bits {
                            either::Either::Left(bits) => bits,
                            either::Either::Right(PointerSized) => {
                                todo!("need ABI in mir for this")
                            }
                        };
                        let next_bb = if !lhs_signed {
                            let lhs = lhs & ((1 << bits) - 1);
                            let rhs = rhs & ((1 << bits) - 1);
                            match u128::cmp(&lhs, &rhs) {
                                std::cmp::Ordering::Less => less_dst,
                                std::cmp::Ordering::Equal => equal_dst,
                                std::cmp::Ordering::Greater => greater_dst,
                            }
                        } else {
                            eprintln!("TODO: signed SwitchCmp const opt");
                            return changed;
                        };
                        block.terminator = Terminator::Goto { target: next_bb };
                        changed = true;
                    }
                }
                _ => {}
            }
        }
        changed
    }
}

/// Sort basic blocks pseudo-topologically. We can't in general sort
/// topologically because there may be back-edges due to control-flow cycles.
///
/// TODO: use a better algorithm. Currently we just use DFS to find a longest
/// non-cyclic path starting from the lowest-numbered non-emitted basic block,
/// then repeat until all blocks have been emitted.
///
/// Example:
/// ```text
/// // Before
/// bb0 {
///     switchBool(_1) [false -> bb2, true -> bb3]
/// }
/// bb1 {
///     return
/// }
/// bb2 {
///     switchBool(_2) [false -> bb1, true -> bb0]
/// }
/// bb3 {
///     goto -> bb2
/// }
/// // After
/// bb0 {
///     switchBool(_1) [false -> bb2, true -> bb1]
/// }
/// bb1 {
///     goto -> bb2
/// }
/// bb2 {
///     switchBool(_2) [false -> bb3, true -> bb0]
/// }
/// bb3 {
///     return
/// }
/// ```
pub struct SortBlocks;

/// Enumerate all control-flow paths in `body` starting from `this_path.last()`
/// and ending either before a basic block where `seen_blocks[i] == true` or
/// with a non-branching terminator.
fn enumerate_paths(
    body: &Body, seen_blocks: &mut [bool], paths: &mut Vec<Vec<BasicBlockIdx>>,
    this_path: &mut Vec<BasicBlockIdx>,
) {
    let start = this_path.last().copied().unwrap();
    match body.basic_blocks[start.0].terminator {
        Terminator::Goto { target } | Terminator::Call { target, .. } => {
            if seen_blocks[target.0] {
                paths.push(this_path.clone());
            } else {
                seen_blocks[target.0] = true;
                this_path.push(target);
                enumerate_paths(body, seen_blocks, paths, this_path);
                this_path.pop();
                seen_blocks[target.0] = false;
            }
        }
        Terminator::SwitchBool { true_dst, false_dst, .. } => {
            if seen_blocks[true_dst.0] && seen_blocks[false_dst.0] {
                paths.push(this_path.clone());
            } else {
                if !seen_blocks[true_dst.0] {
                    seen_blocks[true_dst.0] = true;
                    this_path.push(true_dst);
                    enumerate_paths(body, seen_blocks, paths, this_path);
                    this_path.pop();
                    seen_blocks[true_dst.0] = false;
                }
                if !seen_blocks[false_dst.0] {
                    seen_blocks[false_dst.0] = true;
                    this_path.push(false_dst);
                    enumerate_paths(body, seen_blocks, paths, this_path);
                    this_path.pop();
                    seen_blocks[false_dst.0] = false;
                }
            }
        }
        Terminator::SwitchCmp { less_dst, equal_dst, greater_dst, .. } => {
            if seen_blocks[less_dst.0]
                && seen_blocks[equal_dst.0]
                && seen_blocks[greater_dst.0]
            {
                paths.push(this_path.clone());
            } else {
                if !seen_blocks[less_dst.0] {
                    seen_blocks[less_dst.0] = true;
                    this_path.push(less_dst);
                    enumerate_paths(body, seen_blocks, paths, this_path);
                    this_path.pop();
                    seen_blocks[less_dst.0] = false;
                }
                if !seen_blocks[equal_dst.0] {
                    seen_blocks[equal_dst.0] = true;
                    this_path.push(equal_dst);
                    enumerate_paths(body, seen_blocks, paths, this_path);
                    this_path.pop();
                    seen_blocks[equal_dst.0] = false;
                }
                if !seen_blocks[greater_dst.0] {
                    seen_blocks[greater_dst.0] = true;
                    this_path.push(greater_dst);
                    enumerate_paths(body, seen_blocks, paths, this_path);
                    this_path.pop();
                    seen_blocks[greater_dst.0] = false;
                }
            }
        }
        Terminator::Return | Terminator::Unreachable => {
            paths.push(this_path.clone());
        }
        Terminator::Error => unreachable!(),
    }
}

impl MirOptimization for SortBlocks {
    fn apply(&self, body: &mut Body) -> bool {
        let mut new_block_order = vec![];
        let mut seen_blocks = vec![false; body.basic_blocks.len()];
        while let Some(first_unseen_idx) =
            seen_blocks.iter().position(|block_seen| !block_seen)
        {
            let mut this_path = vec![BasicBlockIdx(first_unseen_idx)];
            let mut paths = vec![];
            seen_blocks[first_unseen_idx] = true;
            enumerate_paths(body, &mut seen_blocks, &mut paths, &mut this_path);
            let longest_path = paths
                .iter()
                .max_by_key(|path| path.len())
                .expect("path should exist");
            new_block_order.extend(longest_path.iter().copied());
            for block in longest_path {
                seen_blocks[block.0] = true;
            }
        }

        debug_assert!(new_block_order.len() == body.basic_blocks.len());
        debug_assert!(
            new_block_order.iter().collect::<HashSet<_>>().len()
                == body.basic_blocks.len()
        );

        // Rearrange the basic blocks according to new_block_order
        let mut new_blocks = vec![];
        for &block in &new_block_order {
            const EMPTY_BLOCK: BasicBlock = BasicBlock {
                operations: vec![],
                terminator: Terminator::Error,
            };
            new_blocks.push(std::mem::replace(
                &mut body.basic_blocks[block.0],
                EMPTY_BLOCK,
            ));
        }
        body.basic_blocks = new_blocks;

        // new_block_order is mapping from new to old, but we need a mapping
        // from old to new to fixup terminators
        let block_idx_mapping: BTreeMap<usize, usize> = new_block_order
            .iter()
            .enumerate()
            .map(|(new, old)| (old.0, new))
            .collect();

        fixup_terminators_after_changing_block_indices(
            &mut body.basic_blocks,
            &block_idx_mapping,
        );

        true
    }
}
