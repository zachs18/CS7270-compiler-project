#![feature(get_many_mut)]

use std::process::ExitCode;

use token::TokenTree;

mod ast;
mod hir;
mod lexer;
mod mir;
mod parser;
mod span;
mod token;
mod util;

fn usage() -> ExitCode {
    println!(
        "USAGE: {} <infile.asm> <outfile.asm>",
        std::env::args().nth(1).as_deref().unwrap_or("riscv-asm")
    );
    ExitCode::FAILURE
}

fn main() -> ExitCode {
    env_logger::Builder::from_env(
        env_logger::Env::default()
            .filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    )
    .format(|buf, record| {
        use std::io::Write;
        writeln!(
            buf,
            "{}:{} {} [{}] - {}",
            record.file().unwrap_or("unknown"),
            record.line().unwrap_or(0),
            buf.timestamp(),
            record.level(),
            record.args()
        )
    })
    .init();

    let args: Vec<_> = std::env::args().collect();
    let Ok([_, infilename, outfilename]) = <[_; 3]>::try_from(args) else {
        return usage();
    };
    let source = if infilename == "-" {
        std::io::read_to_string(std::io::stdin())
    } else {
        std::fs::read_to_string(infilename)
    };
    let source = match source {
        Ok(source) => source,
        Err(err) => {
            eprintln!("FATAL: Failed to read input file: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Leak the source so we can reference it in the tokens and ast without
    // adding lifetimes everywhere.
    let source = String::leak(source);

    let tokens: Vec<TokenTree> = lexer::lex(source.as_bytes());

    dbg!(&tokens);

    let items = parser::parse(&tokens);

    dbg!(&items);

    let (hir, hir_ctx) = hir::lower_ast_to_hir(items);

    dbg!(&hir);

    let mut mir = mir::lower_hir_to_mir(&hir, &hir_ctx);

    println!("pre-opt: ");
    println!("{mir}");

    println!();

    mir.apply_optimization(mir::optimizations::CombineBlocks);

    println!("post-CombineBlocks: ");
    println!("{mir}");

    println!();

    mir.apply_optimization(mir::optimizations::TrimUnreachable);

    println!("post-TrimUnreachable: ");
    println!("{mir}");

    println!();

    mir.apply_optimization(mir::optimizations::RedundantCopyEliminiation);

    println!("post-RedundantCopyEliminiation: ");
    println!("{mir}");

    println!();

    ExitCode::SUCCESS
}

#[test]
fn test_inputs() {
    for source in [
        include_str!("../../input/fibonacci.src"),
        include_str!("../../input/bubblesort.src"),
        include_str!("../../input/collatz.src"),
        include_str!("../../input/patterns.src"),
    ] {
        let tokens = lexer::lex(source.as_bytes());
        let _ast = parser::parse(&tokens);
    }
}
