use std::fs;

use arithma::get_result;
use clap::Parser;

/// arithma is an easy to use, domain-specific programming language for numeric
/// mathematics.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Tells arithma to look at a file instead of a script.
    #[arg(short, long)]
    file: bool,

    /// Pipe mode is a feature that automatically prints out the last printable
    /// value of an arithma script.
    #[arg(short, long)]
    pipe_mode: bool,

    contents: String,
}

fn main() {
    let args = Args::parse();

    let script = if args.file {
        fs::read_to_string(&args.contents).unwrap_or_else(|_| {
            eprintln!("Failed to read the input file '{}'. Perhaps this file does not exist?",
                      &args.contents);
            std::process::exit(1);
        })
    } else {
        args.contents
    };

    if let Err(e) = get_result(&script, args.pipe_mode) {
        eprintln!("{e}");
    }
}
