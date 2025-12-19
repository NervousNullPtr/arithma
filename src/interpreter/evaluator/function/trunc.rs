use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{core::EvalResult, utils::check_arity},
        value::core::Value,
    },
};

/// Truncates a numeric value toward zero.
///
/// Accepts exactly one argument.
/// - Integers are returned unchanged.
/// - Reals use `f64::trunc`.
///
/// Non numeric values cause a `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Integer)` or `Some(Value::Real)` depending on the input.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::trunc::trunc, value::core::Value};
///
/// let r = trunc(&[Value::Real(3.7)], 1).unwrap();
/// assert_eq!(r, 3.0.into());
///
/// let r = trunc(&[Value::Integer(-5)], 1).unwrap();
/// assert_eq!(r, (-5).into());
/// ```
pub fn trunc(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    match args[0] {
        Value::Integer(i) => Ok(Value::Integer(i)),
        Value::Real(r) => Ok(Value::Real(r.trunc())),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}
