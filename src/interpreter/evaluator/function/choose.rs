use crate::{
    error::RuntimeError,
    interpreter::{evaluator::core::EvalResult, value::core::Value},
};

/// Calculates the binomial coefficient of two values, *n* and *k*.
///
/// All three arguments are promoted to real numbers if needed.
/// If `k > n`, an `InvalidArgument` error is returned.
/// The result is returned as an integer.
///
/// # Parameters
/// - `args`: Slice containing `[n, k]`.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Integer)`.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::choose::choose, value::core::Value};
///
/// let result = choose(&[Value::Integer(5), Value::Integer(2)],
///                    1).unwrap();
///
/// assert_eq!(result, 10.into());
/// ```
#[allow(clippy::cast_possible_truncation)]
pub fn choose(args: &[Value], line: usize) -> EvalResult<Value> {
    let n = args[0].clone().as_integer(line)?;
    let k = args[1].clone().as_integer(line)?;

    if n < k {
        return Err(RuntimeError::InvalidArgument { details: format!("For choose(n, k), n must be smaller than or equal to k, but found choose({n}, {k})"), line });
    }

    let k = std::cmp::min(k, n - k);

    let mut result = 1;
    for i in 1..=k {
        result = result * (n - k + i) / i;
    }

    Ok(Value::Integer(result))
}
