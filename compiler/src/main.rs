use std::process::ExitCode;

use token::TokenTree;

mod ast;
mod lexer;
mod parser;
mod parser_nom;
mod span;
mod token;

fn usage() -> ExitCode {
    println!(
        "USAGE: {} <infile.asm> <outfile.asm>",
        std::env::args().nth(1).as_deref().unwrap_or("riscv-asm")
    );
    ExitCode::FAILURE
}

fn main() -> ExitCode {
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

    let tokens: Vec<TokenTree> = lexer::lex(source.as_bytes());

    dbg!(&tokens);

    let items = parser_nom::parse(&tokens);

    dbg!(&items);

    ExitCode::SUCCESS
}
