use crate::interpreter::{
    evaluator::{core::EvalResult, utils::check_arity},
    value::core::Value,
};

/// Prints a value to standard output and returns it unchanged.
///
/// Accepts exactly one argument.
/// The value is formatted using its `Display` implementation.
/// Non-numeric values are allowed since printing works for all `Value`
/// variants.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value)` containing the printed value.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::print::print, value::core::Value};
///
/// // The function prints the value to stdout, but the doctest
/// // only checks the returned result.
/// let result = print(&[Value::Integer(42)], 1).unwrap();
///
/// assert_eq!(result, 42.into());
/// ```
pub fn print(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    println!("{}", args[0]);
    Ok(args[0].clone())
}
