//! Compiling MIR down to RV32I-ISA, ILP32-ABI assembly.
//!
//! Note that we don't support floating-point numbers, so keeping track of the
//! ABI and ISA support for them is just so we produce object-files that work
//! with other software.

use crate::token::Ident;

use super::{CompilationUnit, ItemKind};

#[derive(Debug, Clone, Copy)]
pub struct CompilationState {
    isa: ISA,
    abi: ABI,
}

impl CompilationState {
    pub fn new(isa: ISA, abi: ABI) -> Result<Self, &'static str> {
        match (isa, abi) {
            (ISA::RV32I, ABI::ILP32F | ABI::ILP32D) => {
                Err("cannot use F or D ABI with RV32I")
            }
            (ISA::RV32I | ISA::RV32G, ABI::LP64 | ABI::LP64F | ABI::LP64D) => {
                Err("cannot use 64-bit ABI on RV32")
            }
            (
                ISA::RV64I | ISA::RV64G,
                ABI::ILP32 | ABI::ILP32F | ABI::ILP32D,
            ) => Err("cannot use 32-bit ABI on RV64"),
            (ISA::RV64I, ABI::LP64F | ABI::LP64D) => {
                Err("cannot use F or D ABI on RV64I")
            }
            (ISA::RV32I, ABI::ILP32)
            | (ISA::RV64I, ABI::LP64)
            | (ISA::RV32G, ABI::ILP32 | ABI::ILP32F | ABI::ILP32D)
            | (ISA::RV64G, ABI::LP64 | ABI::LP64F | ABI::LP64D) => {
                Ok(Self { isa, abi })
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ISA {
    RV32I,
    RV32G,
    RV64I,
    RV64G,
}

#[derive(Debug, Clone, Copy)]
pub enum ABI {
    ILP32,
    ILP32F,
    ILP32D,
    LP64,
    LP64F,
    LP64D,
}

impl CompilationUnit {
    pub fn compile(&self, state: CompilationState) -> Vec<u8> {
        let is_64 = match state.abi {
            ABI::ILP32 | ABI::ILP32F | ABI::ILP32D => false,
            ABI::LP64 | ABI::LP64F | ABI::LP64D => true,
        };

        panic!(
            "just emit asm, it's easier than trying to figure out object, and \
             it also means I don't have to emit relocations/relaxations/etc \
             (as difficult-ly)"
        );

        assert!(!is_64, "64-bit unsupported at the moment");

        let mut object_buffer: Vec<u8> = Vec::with_capacity(16384);
        let mut writer = object::write::elf::Writer::new(
            object::Endianness::Little,
            is_64,
            &mut object_buffer,
        );

        for (idx, item) in self.items.iter().enumerate() {
            match item
                .as_ref()
                .left()
                .expect("No stubs should be left after MIR lowering")
            {
                ItemKind::DeclaredExternStatic { name, .. } => {
                    let symbol = writer.add_string(name.ident.as_bytes());

                    todo!()
                }
                ItemKind::DefinedExternStatic {
                    name,
                    mutability,
                    initializer,
                } => todo!(),
                ItemKind::LocalStatic { mutability, initializer } => todo!(),
                ItemKind::DeclaredExternFn { name } => todo!(),
                ItemKind::DefinedExternFn { name, body } => todo!(),
                ItemKind::LocalFn { body } => todo!(),
                ItemKind::StringLiteral { data } => todo!(),
            }
        }

        if true {
            todo!("draw the owl");
        }

        object_buffer
    }
}
