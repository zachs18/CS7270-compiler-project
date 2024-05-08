use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

use tempfile::TempDir;

fn usage() -> ! {
    eprintln!("Usage:");
    eprintln!("\tcargo run --bin runner -- [source files] -- [args]");
    std::process::exit(-1)
}

fn compile_file(
    filename: &Path, build_dir: &TempDir,
) -> Result<PathBuf, Box<dyn std::error::Error>> {
    let asm_file =
        tempfile::Builder::new().suffix(".s").tempfile_in(build_dir.path())?;
    let compile_command_status = Command::new("cargo")
        .args(["run", "--bin", "compiler", "--"])
        .args([filename, asm_file.path()])
        .status()?;
    if compile_command_status.success() {
        Ok(asm_file.keep()?.1)
    } else {
        Err(format!("failed to compile {filename:?}").into())
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    let program_args = match args.iter().position(|arg| arg == "--") {
        Some(position) => {
            let program_args = args.split_off(position + 1);
            args.pop();
            program_args
        }
        None => vec![],
    };

    if args.iter().any(|arg| arg.starts_with("--")) {
        usage()
    }

    let mut source_files = vec![];
    let mut c_source_files = vec![];

    for file in args {
        let file = PathBuf::from(file);
        match file.extension().and_then(OsStr::to_str) {
            Some("src") => source_files.push(file),
            Some("c") => c_source_files.push(file),
            _ => panic!(
                "source files should end in .src, C helper files should end \
                 in .c"
            ),
        }
    }

    let build_dir =
        tempfile::tempdir().expect("Failed to create build directory");
    let asm_files: Vec<_> = source_files
        .iter()
        .map(|filename| compile_file(filename, &build_dir))
        .collect::<Result<_, _>>()
        .expect("failed to compile source files");
    // If any files failed to compile, pass them through directly to gcc
    let compiler_files: Vec<&_> =
        asm_files.iter().chain(&c_source_files).collect();

    let executable_file = build_dir.path().join("main");

    let gcc_command_status = Command::new("riscv64-linux-gnu-gcc")
        .arg("-o")
        .arg(executable_file.as_path())
        .args(compiler_files)
        .status()
        .expect("failed to compile executable");

    assert!(gcc_command_status.success(), "failed to compile executable");

    let qemu_command_status = Command::new("qemu-riscv64")
        .args(["-L", "/usr/riscv64-linux-gnu/"])
        .arg(executable_file.as_path())
        .arg("--")
        .args(program_args)
        .status()
        .expect("failed to run executable");

    println!("qemu returned {:?}", qemu_command_status.code());
}
