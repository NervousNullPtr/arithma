use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::core::EvalResult,
        value::{complex::ComplexNumber, core::Value},
    },
};

/// Computes square roots and n-th roots for numeric values.
///
/// - With one argument:
///   - Nonnegative integers and reals return a real square root.
///   - Negative integers and reals return a purely imaginary complex result.
///   - Complex values use their complex square root.
/// - With two arguments: Computes the n-th root: `args[0]^(1 / args[1])`. The
///   exponent must be numeric, and zero is not permitted as the root.
///
/// Non-numeric inputs produce an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice of one or two numeric arguments.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// A real or complex value depending on the input.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::sqrt::sqrt, value::core::Value};
///
/// // Simple real square root
/// let r = sqrt(&[Value::Real(9.0)], 1).unwrap();
/// assert_eq!(r, 3.0.into());
///
/// // 4th root of 16 -> 2
/// let r = sqrt(&[Value::Real(16.0), Value::Real(4.0)], 1).unwrap();
/// assert_eq!(r, 2.0.into());
/// ```
pub fn sqrt(args: &[Value], line: usize) -> EvalResult<Value> {
    match args.len() {
        1 => match args[0] {
            Value::Integer(n) if n >= 0 => Ok(Value::Real(args[0].as_real(line)?.sqrt())),
            Value::Integer(_) => {
                let imag = (-(args[0].as_real(line)?)).sqrt();
                Ok(Value::Complex(ComplexNumber { real:      0.0,
                                                  imaginary: imag, }))
            },

            Value::Real(x) if x >= 0.0 => Ok(Value::Real(x.sqrt())),
            Value::Real(x) => {
                let imag = (-x).sqrt();
                Ok(Value::Complex(ComplexNumber { real:      0.0,
                                                  imaginary: imag, }))
            },

            Value::Complex(c) => Ok(c.sqrt().checked_as_real()),

            _ => Err(RuntimeError::ExpectedNumber { line }),
        },
        2 => {
            let base = match &args[0] {
                Value::Complex(c) => *c,
                Value::Real(r) => ComplexNumber::from(*r),
                Value::Integer(_) => ComplexNumber::from(args[0].as_real(line)?),
                _ => return Err(RuntimeError::ExpectedNumber { line }),
            };

            let root = match &args[1] {
                Value::Real(r) => *r,
                Value::Integer(_) => args[1].as_real(line)?,
                _ => return Err(RuntimeError::ExpectedNumber { line }),
            };

            if root == 0.0 {
                return Err(RuntimeError::DivisionByZero { line });
            }

            let c = base.powf(1.0 / root);
            Ok(c.checked_as_real())
        },
        _ => Err(RuntimeError::ArgumentCountMismatch { line }),
    }
}
