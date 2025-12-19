/// The evaluator module executes AST nodes and computes results.
///
/// The evaluator traverses the AST, evaluates expressions and statements,
/// performs arithmetic and logical operations, manages variable state, and
/// produces results. It is the core execution engine of the interpreter.
///
/// # Responsibilities
/// - Evaluates AST nodes, performing all supported operations.
/// - Handles variables, functions, and control flow (if applicable).
/// - Reports runtime errors such as division by zero or invalid operations.
pub mod evaluator;
/// The lexer module tokenizes source code for further parsing.
///
/// The lexer (tokenizer) reads the raw source text and produces a stream of
/// tokens, each corresponding to meaningful language elements such as numbers,
/// identifiers, operators, delimiters, and keywords. This is the first stage of
/// interpretation.
///
/// # Responsibilities
/// - Converts the input character stream into tokens with type and source
///   location.
/// - Handles numeric and string literals, identifiers, and operators.
/// - Reports lexical errors for invalid or malformed input.
pub mod lexer;
/// The parser module builds the abstract syntax tree (AST) from tokens.
///
/// The parser processes the token stream produced by the lexer and constructs
/// an AST that represents the syntactic structure of expressions and
/// statements. This enables later phases to analyze and execute user code.
///
/// # Responsibilities
/// - Converts tokens into structured AST nodes (expressions, statements).
/// - Validates correct grammar and syntax, reporting errors with location info.
/// - Supports arithmetic, function calls, assignments, and more.
pub mod parser;
/// The value module defines the runtime data types for evaluation.
///
/// This module declares all the value types used during interpretation and
/// execution, such as integers, floating-point numbers, booleans, strings,
/// sets, arrays, and complex numbers. It also provides methods for type
/// conversion, promotion, and comparison, ensuring robust type handling
/// throughout evaluation.
///
/// # Responsibilities
/// - Defines the `Value` enum and all supported value variants.
/// - Implements methods for arithmetic, logic, conversion, and error checking.
/// - Provides safe promotion between numeric types (e.g., integer to real).
pub mod value;
