use std::{fs, io::{self, Read}};

use arithma::get_result;
use clap::Parser;

/// arithma is an easy to use, domain-specific programming language for numeric
/// mathematics.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Tells arithma to look at a file instead of a script.
    #[arg(short, long)]
    file_mode: bool,

    /// Auto print is a feature that automatically prints out the last printable
    /// value of an arithma script.
    #[arg(short = 'p', long)]
    auto_print: bool,
    
    contents: Option<String>,
}

fn main() {
    let args = Args::parse();

    let script = if args.file_mode {
        fs::read_to_string(args.contents.as_ref().unwrap()).unwrap_or_else(|_| {
            eprintln!("Failed to read the input file '{}'. Perhaps this file does not exist?",
                      args.contents.as_ref().unwrap());
            std::process::exit(1);
        })
    } else if let Some(contents) = args.contents {
        contents
    } else {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).unwrap_or_else(|_| {
            eprintln!("Failed to read from stdin.");
            std::process::exit(1);
        });
        
        buffer
    };

    if let Err(e) = get_result(&script, args.auto_print) {
        eprintln!("{e}");
    }
}
