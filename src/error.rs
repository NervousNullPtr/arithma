/// Parsing errors.
///
/// Defines all error types that can occur during lexing and parsing of source
/// code. Parse errors include syntax mistakes, unexpected tokens, invalid
/// literals, and any other issues detected before evaluation.
pub mod parse_error;
/// Runtime errors.
///
/// Contains all error types that can be raised during evaluation and execution.
/// Runtime errors include things like division by zero, type mismatches,
/// invalid operations, or failed numeric conversions.
pub mod runtime_error;

pub use parse_error::ParseError;
pub use runtime_error::RuntimeError;
