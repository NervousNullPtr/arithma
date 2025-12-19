use crate::interpreter::{
    evaluator::{core::EvalResult, utils::check_arity},
    value::core::Value,
};

/// Computes the minimum or maximum of two numeric values.
///
/// Both arguments are promoted to real numbers if needed.  
/// - If both promoted values remain integers, the result is an integer.
/// - Otherwise the comparison is performed on real values.
///
/// The operation is selected by the `name` parameter, which must be `"min"` or
/// `"max"`. Any non-numeric argument produces an `ExpectedNumber` error.
///
/// # Parameters
/// - `name`: Either `"min"` or `"max"`.
/// - `args`: Slice containing exactly two arguments.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Integer)` or `Some(Value::Real)` depending on input types.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::min_max::min_max, value::core::Value};
///
/// let r = min_max("min", &[Value::Integer(3), Value::Integer(7)], 1).unwrap();
/// assert_eq!(r, 3.into());
///
/// let r = min_max("max", &[Value::Real(2.5), Value::Real(1.0)], 1).unwrap();
/// assert_eq!(r, 2.5.into());
/// ```
pub fn min_max(name: &str, args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 2, line)?;

    let (left, right) = args[0].clone().promote_to_real(&args[1], line)?;

    let result = if let (Value::Integer(a), Value::Integer(b)) = (&left, &right) {
        let value = if name == "min" {
            std::cmp::min(a, b)
        } else {
            std::cmp::max(a, b)
        };
        Value::Integer(*value)
    } else {
        let left = left.as_real(line)?;
        let right = right.as_real(line)?;
        let value = if name == "min" {
            left.min(right)
        } else {
            left.max(right)
        };
        Value::Real(value)
    };

    Ok(result)
}
