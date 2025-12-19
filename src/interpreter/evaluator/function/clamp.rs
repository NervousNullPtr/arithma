use crate::{
    error::RuntimeError,
    interpreter::{evaluator::core::EvalResult, value::core::Value},
};

/// Clamps a numeric value between a minimum and maximum bound.
///
/// All three arguments are promoted to real numbers if needed.
/// If `min > max`, an `InvalidArgument` error is returned.
/// The result is returned as an integer when all inputs are integers and the
/// clamped value has no fractional part; otherwise a real value is produced.
///
/// # Parameters
/// - `args`: Slice containing `[min, value, max]`.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Integer)` or `Some(Value::Real)` depending on input types.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::clamp::clamp, value::core::Value};
///
/// let result = clamp(&[Value::Integer(0), Value::Integer(5), Value::Integer(3)],
///                    1).unwrap();
///
/// // 5 clamped between 0 and 3 yields 3
/// assert_eq!(result, 3.into());
/// ```
#[allow(clippy::cast_possible_truncation)]
pub fn clamp(args: &[Value], line: usize) -> EvalResult<Value> {
    let (min, val) = args[0].clone().promote_to_real(&args[1], line)?;
    let (min, max) = min.promote_to_real(&args[2], line)?;

    let min_f = min.as_real(line)?;
    let max_f = max.as_real(line)?;
    let val_f = val.as_real(line)?;

    if min_f > max_f {
        return Err(RuntimeError::InvalidArgument { details: format!("clamp: min ({min_f}) > max ({max_f})"),
                                                   line });
    }

    let clamped = if val_f < min_f {
        min_f
    } else if val_f > max_f {
        max_f
    } else {
        val_f
    };

    if min.is_integer() && val.is_integer() && max.is_integer() && clamped.fract() == 0.0 {
        Ok(Value::Integer(clamped as i64))
    } else {
        Ok(Value::Real(clamped))
    }
}
