use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{core::EvalResult, utils::check_arity},
        value::{complex::ComplexNumber, core::Value},
    },
};

/// Computes the logarithm of a value with respect to a given base.
///
/// Accepts exactly two arguments: `value` and `base`.
/// Both are converted to complex numbers before computing:
/// `log_base(value) = ln(value) / ln(base)`.
///
/// Division by zero occurs when `ln(base)` equals zero.
/// Non-numeric arguments produce an `ExpectedNumber` error.
///
/// # Example
/// ```
/// use arithma::interpreter::{
///     evaluator::function::log::log,
///     value::{complex::ComplexNumber, core::Value},
/// };
///
/// // log_e(e) = 1
/// let e = std::f64::consts::E;
///
/// let result = log(&[Value::Real(e), Value::Real(e)], 1).unwrap();
///
/// assert_eq!(result,
///            Value::Complex(ComplexNumber { real:      1.0,
///                                           imaginary: 0.0, }));
/// ```
pub fn log(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 2, line)?;

    let base = to_complex(&args[1], line)?;
    let value = to_complex(&args[0], line)?;

    let ln_base = base.ln();
    let ln_value = value.ln();

    if ln_base.real == 0.0 && ln_base.imaginary == 0.0 {
        return Err(RuntimeError::DivisionByZero { line });
    }

    Ok(Value::Complex(ln_value / ln_base))
}

/// Converts a numeric value to a complex number.
///
/// Integers and reals are converted to complex numbers with zero imaginary
/// part. Complex values are returned unchanged.
/// Non-numeric values yield an `ExpectedNumber` error.
///
/// # Parameters
/// - `value`: Value to convert.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// A `ComplexNumber` extracted or derived from the value.
///
/// # Example
/// ```
/// use arithma::interpreter::{
///     evaluator::function::log::to_complex,
///     value::{complex::ComplexNumber, core::Value},
/// };
///
/// let c = to_complex(&Value::Real(5.0), 1).unwrap();
/// assert_eq!(c,
///            ComplexNumber { real:      5.0,
///                            imaginary: 0.0, });
/// ```
pub fn to_complex(value: &Value, line: usize) -> EvalResult<ComplexNumber> {
    match value {
        Value::Complex(c) => Ok(*c),
        Value::Real(r) => Ok(ComplexNumber::from(*r)),
        Value::Integer(_) => Ok(ComplexNumber::from(value.as_real(line)?)),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}
