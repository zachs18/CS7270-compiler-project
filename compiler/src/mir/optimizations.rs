//! Optimizations on MIR, including
//!
//! * Combining blocks

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use itertools::Itertools;
use petgraph::{
    graph::DiGraph,
    graphmap::{DiGraphMap, GraphMap},
    Graph,
};

use crate::mir::{self, BasicBlock, BasicBlockIdx, Terminator};

pub trait MirOptimization {
    /// Returns `true` if any changes occurred.
    fn apply(&self, body: &mut mir::Body) -> bool;
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
    fn apply(&self, body: &mut mir::Body) -> bool {
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
                    mir::Terminator::Goto { target } => {
                        control_flow_graph.add_edge(
                            src,
                            target,
                            BranchKind::Goto,
                        );
                    }
                    mir::Terminator::SwitchBool {
                        true_dst, false_dst, ..
                    } => {
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
                    mir::Terminator::SwitchCmp {
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
                    mir::Terminator::Call { target, .. } => {
                        control_flow_graph.add_edge(
                            src,
                            target,
                            BranchKind::Call,
                        );
                    }
                    mir::Terminator::Return | mir::Terminator::Unreachable => {
                        // no edge to add
                    }
                    mir::Terminator::Error => {
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
pub struct TrimUnreachable;

impl MirOptimization for TrimUnreachable {
    fn apply(&self, body: &mut mir::Body) -> bool {
        let mut reachable = vec![false; body.basic_blocks.len()];
        reachable[0] = true;
        let mut frontier: VecDeque<BasicBlockIdx> =
            VecDeque::from([BasicBlockIdx(0)]);

        // Breadth-first floodfill to find all reachable blocks
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

        while let Some(idx) = frontier.pop_front() {
            match body.basic_blocks[idx.0].terminator {
                Terminator::Goto { target } => insert_frontier!(target),
                Terminator::SwitchBool { true_dst, false_dst, .. } => {
                    insert_frontier!(true_dst, false_dst)
                }
                Terminator::SwitchCmp {
                    less_dst,
                    equal_dst,
                    greater_dst,
                    ..
                } => {
                    insert_frontier!(less_dst, equal_dst, greater_dst)
                }
                Terminator::Call { target, .. } => insert_frontier!(target),
                Terminator::Return | Terminator::Unreachable => {
                    // no other blocks to reach
                }
                Terminator::Error => {
                    unreachable!("Terminator::Error after MIR-building")
                }
            }
        }

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

        for block in &mut body.basic_blocks {
            match &mut block.terminator {
                Terminator::Goto { target } => fixup_block_idx!(target),
                Terminator::SwitchBool { true_dst, false_dst, .. } => {
                    fixup_block_idx!(true_dst, false_dst)
                }
                Terminator::SwitchCmp {
                    less_dst,
                    equal_dst,
                    greater_dst,
                    ..
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

        true
    }
}
