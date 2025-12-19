//! # arithma
//!
//! arithma is a mathematical expression interpreter written in Rust.
//! It parses, analyzes, and evaluates mathematical expressions with support for
//! variables, functions, sets, arrays, tolerances, and more.

#![warn(
    clippy::redundant_clone,
    clippy::needless_pass_by_value,
    clippy::similar_names,
    clippy::large_enum_variant,
    clippy::string_lit_as_bytes,
    clippy::match_same_arms,
    clippy::cargo,
    clippy::nursery,
    clippy::perf,
    clippy::style,
    clippy::suspicious,
    clippy::correctness,
    clippy::complexity,
    clippy::pedantic,
    //missing_docs,
)]
#![allow(clippy::missing_errors_doc)]

use std::collections::HashSet;

use logos::Logos;

use crate::{
    error::ParseError,
    interpreter::{
        evaluator::core::Context,
        lexer::{LexerExtras, Token},
        parser::statement::parse_statement,
    },
};

/// Defines the structure of parsed code.
///
/// This module declares the `Expr` enum and related types that represent the
/// syntactic structure of source code as a tree. The AST is built by the parser
/// and traversed by the evaluator.
///
/// # Responsibilities
/// - Defines expression and statement types for all language constructs.
/// - Attaches metadata (such as source locations) to AST nodes for error
///   reporting.
/// - Enables extensible and robust handling of parsed code.
pub mod ast;
/// Provides unified error types for parsing and evaluation.
///
/// This module defines all errors that can be raised during lexing, parsing, or
/// evaluating code. It standardizes error reporting and carries detailed
/// information about failures, including error kinds, descriptions, and source
/// locations for debugging and user feedback.
///
/// # Responsibilities
/// - Defines error enums for all failure modes (lexer, parser, evaluator).
/// - Attaches line numbers and detailed messages for context.
/// - Supports integration with standard error handling traits and reporting
///   utilities.
pub mod error;
/// Orchestrates the entire process of code execution.
///
/// This module ties together lexing, parsing, evaluation, value
/// representations, error handling, and all supporting infrastructure to
/// provide a complete runtime for source code evaluation. It exposes the public
/// API for interpreting and executing expressions or programs.
///
/// # Responsibilities
/// - Coordinates all core components: lexer, parser, evaluator, and value
///   types.
/// - Provides entry points for parsing and evaluating user code.
/// - Manages the flow of data and errors between phases.
pub mod interpreter;
/// General utilities for safe numeric conversion and helpers.
///
/// This module provides reusable helpers and conversion routines that are used
/// throughout the interpreter, parser, and evaluator. These include safe
/// conversions between integer and floating-point types, and any
/// general-purpose functions not specific to a single phase.
///
/// # Responsibilities
/// - Safely convert between `i64`, `u64`, `usize`, and `f64` without silent
///   data loss.
/// - Provide general utility functions used in multiple modules.
pub mod util;

/// Returns the final evaluation result after execution.
///
/// This function parses and executes all statements in the provided source
/// string using the interpreter's evaluation context. If execution succeeds, it
/// returns `Ok(())`; otherwise, it returns an error with details about the
/// failure.
///
/// # Errors
/// Returns an error if parsing or evaluation fails, or if any runtime error
/// occurs.
///
/// # Examples
/// ```
/// use arithma::get_result;
///
/// // Simple expression: the result will be calculated and no error should occur.
/// let source = "let result = 2 + 2";
/// let res = get_result(source, false);
/// assert!(res.is_ok());
///
/// // Example with an intentional error (unknown variable).
/// let source = "let y = x + 1"; // 'x' is not defined
/// let res = get_result(source, false);
/// assert!(res.is_err());
/// ```
pub fn get_result(source: &str, auto_print: bool) -> Result<(), Box<dyn std::error::Error>> {
    let mut context = Context::new();

    let mut tokens = Vec::new();
    let mut lexer = Token::lexer_with_extras(source, LexerExtras { line: 1 });

    while let Some(token) = lexer.next() {
        if let Ok(tok) = token {
            tokens.push((tok, lexer.extras.line));
        } else {
            let slice = lexer.slice();
            return Err(Box::new(ParseError::UnexpectedToken { token: slice.to_string(),
                                                              line:  lexer.extras.line, }));
        }
    }

    let mut iter = tokens.iter().peekable();

    let mut result = None;

    while iter.peek().is_some() {
        while let Some((Token::NewLine, _)) = iter.peek() {
            iter.next();
        }
        if iter.peek().is_none() {
            break;
        }
        match parse_statement(&mut iter) {
            Ok(statement) => match context.eval_statement(&statement, None, &HashSet::new()) {
                Ok(value) => {
                    if value.is_some() {
                        result = value;
                    }
                },
                Err(e) => return Err(Box::new(e)),
            },
            Err(e) => return Err(Box::new(e)),
        }
    }

    if auto_print && let Some(v) = result {
        println!("{v}");
    }

    Ok(())
}
