use crate::{
    hir::TypeKind,
    mir::{
        BasicBlockIdx, BasicOperation, Body, CompilationUnit, Constant,
        Operand, Place, SlotIdx, Terminator, TypeIdx, Value,
    },
};

use super::CompilationState;

#[derive(Debug, Clone)]
enum ConstEvalValue {
    Uninit,
    Integer { value: u128 },
    Bool { value: bool },
}

impl ConstEvalValue {
    fn from_constant(c: &Constant) -> Self {
        match *c {
            Constant::Integer(value) => Self::Integer { value },
            Constant::Bool(value) => Self::Bool { value },
            Constant::Tuple(_) => todo!(),
            Constant::ItemAddress(_) => todo!(),
        }
    }
}

impl CompilationUnit {
    fn finalize_value(
        &self, value: &ConstEvalValue, ty: TypeIdx, state: &CompilationState,
    ) -> Vec<u8> {
        match value {
            ConstEvalValue::Uninit => {
                unreachable!("should not have uninit in final const eval value")
            }
            ConstEvalValue::Integer { value } => {
                let layout = self.layout(ty, state);
                let mut bytes = vec![0; layout.size()];
                let value = value.to_le_bytes();
                bytes.copy_from_slice(&value[..layout.size()]);
                bytes
            }
            &ConstEvalValue::Bool { value } => vec![value as u8],
        }
    }

    pub fn const_eval(&self, body: &Body, state: &CompilationState) -> Vec<u8> {
        assert_eq!(body.argc, 0, "cannot const-eval functions, only statics");

        let mut slots: Vec<ConstEvalValue> =
            vec![ConstEvalValue::Uninit; body.slots.len()];

        let mut next_bb = BasicBlockIdx(0);
        let mut op_count: usize = 0;
        const OP_LIMIT: usize = 1_000_000; // arbitrary

        fn assert_local_place(place: &Place) -> SlotIdx {
            if place.projection.is_some() {
                panic!("cannot const-eval non-local assignments (yet)");
            }
            place.local
        }

        'eval_loop: loop {
            if op_count >= OP_LIMIT {
                panic!(
                    "const-eval stopping after {OP_LIMIT} steps; maybe \
                     there's an infinite loop in a static initializer?"
                );
            }
            let block = &body.basic_blocks[next_bb.0];
            for op in &block.operations {
                op_count += 1;
                match op {
                    BasicOperation::Nop => {}
                    BasicOperation::Assign(dst, value) => {
                        let dst = assert_local_place(dst);
                        let value = match value {
                            Value::Operand(Operand::Constant(value)) => {
                                ConstEvalValue::from_constant(value)
                            }
                            Value::Operand(Operand::Copy(src)) => {
                                let slot = assert_local_place(src);
                                slots[slot.0].clone()
                            }
                            Value::BinaryOp(_, _, _) => todo!(),
                            Value::Not(_) => todo!(),
                            Value::Negate(_) => todo!(),
                        };
                        slots[dst.0] = value;
                    }
                }
            }
            match &block.terminator {
                &Terminator::Goto { target } => next_bb = target,
                &Terminator::SwitchBool { scrutinee, true_dst, false_dst } => {
                    match slots[scrutinee.0] {
                        ConstEvalValue::Bool { value: true } => {
                            next_bb = true_dst
                        }
                        ConstEvalValue::Bool { value: false } => {
                            next_bb = false_dst
                        }
                        _ => unreachable!(
                            "invalid switchbool scrutinee in const eval"
                        ),
                    }
                }
                Terminator::SwitchCmp {
                    lhs,
                    rhs,
                    less_dst,
                    equal_dst,
                    greater_dst,
                } => todo!(),
                Terminator::Return => break 'eval_loop,
                Terminator::Unreachable => {
                    unreachable!("entered unreachable code during const-eval")
                }
                Terminator::Call { func, args, return_destination, target } => {
                    unimplemented!(
                        "cannot currently call functions in const-eval"
                    )
                }
                Terminator::Error => unreachable!(),
            }
        }

        self.finalize_value(&slots[0], body.slots[0], state)
    }
}
