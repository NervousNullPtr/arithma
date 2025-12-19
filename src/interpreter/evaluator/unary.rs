use crate::{
    ast::UnaryOperator,
    error::RuntimeError,
    interpreter::{
        evaluator::{
            core::{Context, EvalResult},
            utils::{euler_gamma, multi_factorial},
        },
        value::core::Value,
    },
    util::num::{f64_to_u64_checked, u64_to_f64_checked},
};

impl Context {
    /// Evaluates a unary operation on a value.
    ///
    /// Supported operators:
    /// - `Negate`: numeric negation for integers, reals and complex numbers.
    /// - `Not`: boolean negation.
    /// - `Factorial(n)`: standard factorial (`n = 1`) or multi-factorial (`n >
    ///   1`). Multi-factorials require non-negative integer input. For
    ///   non-integer positive values, the factorial is computed using the gamma
    ///   function (`Γ(x + 1)`).
    ///
    /// Invalid types or invalid domains (negative integers for factorial,
    /// invalid multi-factorial arguments) produce detailed errors.
    ///
    /// # Parameters
    /// - `op`: Unary operator.
    /// - `value`: Input value.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// The computed `Value` wrapped in `EvalResult`.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::UnaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// // Negation
    /// let v = Context::eval_unary(UnaryOperator::Negate, &Value::Integer(5), 1).unwrap();
    /// assert_eq!(v, Value::Integer(-5));
    ///
    /// // Boolean not
    /// let v = Context::eval_unary(UnaryOperator::Not, &Value::Bool(false), 1).unwrap();
    /// assert_eq!(v, Value::Bool(true));
    ///
    /// // Factorial: 4! = 24
    /// let v = Context::eval_unary(UnaryOperator::Factorial(1), &Value::Integer(4), 1).unwrap();
    /// assert_eq!(v.as_real(1).unwrap(), 24.0);
    /// ```
    pub fn eval_unary(op: UnaryOperator, value: &Value, line: usize) -> EvalResult<Value> {
        match op {
            UnaryOperator::Negate => match value {
                Value::Integer(n) => Ok(Value::Integer(-n)),
                Value::Real(r) => Ok(Value::Real(-r)),
                Value::Complex(i) => Ok(Value::Complex(-*i)),
                _ => Err(RuntimeError::ExpectedNumber { line }),
            },
            UnaryOperator::Not => Ok(Value::Bool(!value.as_bool(line)?)),
            UnaryOperator::Factorial(n) => {
                let x = match value {
                    Value::Real(x) => *x,
                    Value::Integer(_) => value.as_real(line)?,
                    _ => {
                        return Err(RuntimeError::TypeError { details: format!("Factorial not defined for {value}"),
                                                             line });
                    },
                };

                if n > 1 && (x.fract() != 0.0 || x < 0.0) {
                    let formatted_x = if x.fract() == 0.0 && x >= 0.0 {
                        format!("{}", f64_to_u64_checked(x, line)?)
                    } else {
                        x.to_string()
                    };
                    return Err(RuntimeError::InvalidArgument { details:
                                                                   format!("Multi-factorial is only defined for non-negative integers, but found {}",
                                                                           formatted_x
                                                                           + &"!".repeat(n
                                                                                         as usize)),
                                                               line });
                }

                if x.fract() == 0.0 && x < 0.0 {
                    return Err(RuntimeError::InvalidArgument { details: format!("Factorial not defined for negative integer {x}"),
                                                               line });
                }

                if x.fract() == 0.0 && x >= 0.0 {
                    let mfact = multi_factorial(f64_to_u64_checked(x, line)?, n, line)?;
                    return Ok(Value::Real(u64_to_f64_checked(mfact, line)?));
                }

                Ok(Value::Real(euler_gamma(x + 1.0, line)?))
            },
        }
    }
}
