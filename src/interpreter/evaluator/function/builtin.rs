use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{core::EvalResult, utils::check_arity},
        value::{complex::ComplexNumber, core::Value},
    },
};

/// Applies a unary builtin function to a numeric value.
///
/// The generated functions accept exactly one argument.  
/// - Integers are converted to real numbers before applying the real function.
/// - Reals use the corresponding real builtin.
/// - Complex values use the complex variant.
///
/// Non-numeric arguments produce an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// An `EvalResult<Value>` containing the computed value.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::sin, value::core::Value};
///
/// let x = Value::Real(std::f64::consts::PI / 2.0);
/// let r = sin(&[x], 1).unwrap();
///
/// assert_eq!(r, Value::Real(1.0));
/// ```
macro_rules! real_complex_builtin {
    ($fname:ident, $real_fn:ident, $complex_fn:ident) => {
        pub fn $fname(args: &[Value], line: usize) -> EvalResult<Value> {
            check_arity(args, 1, line)?;

            match args[0] {
                Value::Integer(_) => Ok(Value::Real((args[0].as_real(line)?.$real_fn().into()))),
                Value::Real(r) => Ok(Value::Real(r.$real_fn().into())),
                Value::Complex(c) => Ok(Value::Complex(ComplexNumber::$complex_fn(c))),
                _ => Err(RuntimeError::ExpectedNumber { line }),
            }
        }
    };
}

real_complex_builtin!(ln, ln, ln);
real_complex_builtin!(sin, sin, sin);
real_complex_builtin!(cos, cos, cos);
real_complex_builtin!(tan, tan, tan);
real_complex_builtin!(exp, exp, exp);
real_complex_builtin!(sinh, sinh, sinh);
real_complex_builtin!(cosh, cosh, cosh);
real_complex_builtin!(tanh, tanh, tanh);

/// Converts a numeric value from degrees to radians.
///
/// Accepts exactly one argument.
/// Integers are converted to real numbers before applying the conversion.
/// Non-numeric values cause an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Value::Real` containing the angle in radians.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::radians, value::core::Value};
///
/// let r = radians(&[Value::Real(180.0)], 1).unwrap();
/// assert_eq!(r, Value::Real(std::f64::consts::PI));
/// ```
pub fn radians(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    match args[0] {
        Value::Integer(_) | Value::Real(_) => Ok(Value::Real(args[0].as_real(line)?.to_radians())),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}

/// Converts a numeric value from radians to degrees.
///
/// Accepts exactly one argument.
/// Integers are converted to real numbers before applying the conversion.
/// Non-numeric values cause an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Value::Real` containing the angle in degrees.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::degrees, value::core::Value};
///
/// let d = degrees(&[Value::Real(std::f64::consts::PI)], 1).unwrap();
/// assert_eq!(d, Value::Real(180.0));
/// ```
pub fn degrees(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    match args[0] {
        Value::Integer(_) | Value::Real(_) => Ok(Value::Real(args[0].as_real(line)?.to_degrees())),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}

/// Returns the numeric sign of a value.
///
/// Accepts exactly one argument.
/// Integers return `-1`, `0` or `1`.
/// Reals return `-1.0`, `0.0` or `1.0`.
/// Non-numeric values cause an `ExpectedNumber` error.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Value::Integer` or `Value::Real` depending on input type.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::sign, value::core::Value};
///
/// let s = sign(&[Value::Integer(-42)], 1).unwrap();
/// assert_eq!(s, Value::Integer(-1));
/// ```
pub fn sign(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    match args[0] {
        Value::Integer(_) | Value::Real(_) => args[0].sign(line),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}

/// Asserts that a boolean argument is true.
///
/// Accepts exactly one argument.
/// If the value is false, an `AssertionFailed` error is returned.
/// If it is true, the function returns the value unchanged.
///
/// # Parameters
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Value::Bool(true)` on success.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::assert_fn, value::core::Value};
///
/// let r = assert_fn(&[Value::Bool(true)], 1).unwrap();
/// assert_eq!(r, Value::Bool(true));
/// ```
pub fn assert_fn(args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    if !args[0].as_bool(line)? {
        return Err(RuntimeError::AssertionFailed { line });
    }
    Ok(args[0].clone())
}

/// Applies a rounding operation (`floor`, `ceil`, or `round`) to a numeric
/// value.
///
/// The operation is selected by name.
/// Integers are returned as-is.
/// Non-numeric values cause an `ExpectedNumber` error.
///
/// # Parameters
/// - `name`: Operation name (`floor`, `ceil`, `round`).
/// - `args`: Slice containing one argument.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Value::Real` or `Value::Integer` depending on input.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::builtin::unary_round, value::core::Value};
///
/// let r = unary_round("floor", &[Value::Real(3.8)], 1).unwrap();
/// assert_eq!(r, Value::Real(3.0));
/// ```
pub fn unary_round(name: &str, args: &[Value], line: usize) -> EvalResult<Value> {
    check_arity(args, 1, line)?;

    let op = match name {
        "floor" => f64::floor,
        "ceil" => f64::ceil,
        "round" => f64::round,
        _ => unreachable!(),
    };

    match args[0] {
        Value::Integer(i) => Ok(Value::Integer(i)),
        Value::Real(r) => Ok(Value::Real(op(r))),
        _ => Err(RuntimeError::ExpectedNumber { line }),
    }
}
