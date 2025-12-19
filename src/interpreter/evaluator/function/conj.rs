use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{core::EvalResult, utils::check_arity},
        value::core::Value,
    },
};
/// Returns the complex conjugate of a numeric value.
///
/// Accepts exactly one argument.
/// - Complex numbers return their conjugate.
/// - Real and integer values are returned unchanged.
///
/// Non-numeric arguments yield an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Complex)` for complex input or `Some(Value::Real/Integer)` for
/// real input.
///
/// # Example
/// ```
/// use arithma::interpreter::{
///     evaluator::function::conj::conj,
///     value::{complex::ComplexNumber, core::Value},
/// };
///
/// let z = Value::Complex(ComplexNumber { real:      3.0,
///                                        imaginary: -4.0, });
/// let r = conj(&[z.clone()], 1).unwrap();
///
/// assert_eq!(r,
///            Value::Complex(ComplexNumber { real:      3.0,
///                                           imaginary: 4.0, }));
/// ```
pub fn conj(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    match args[0] {
        Value::Complex(c) => Ok(Value::Complex(c.conj())),
        Value::Real(r) => Ok(Value::Real(r)),
        Value::Integer(i) => Ok(Value::Integer(i)),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}
