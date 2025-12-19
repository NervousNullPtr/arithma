use crate::{
    ast::BinaryOperator,
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::{complex::ZERO, core::Value},
    },
};

impl Context {
    /// Evaluates a scalar arithmetic operation.
    ///
    /// The function handles integer, real and complex operands. Mixed types are
    /// promoted as needed. Division by zero is checked explicitly for all
    /// numeric categories. The operator must be one of `Add`, `Sub`, `Mul` or
    /// `Div`; other operators are not processed here.
    ///
    /// # Parameters
    /// - `op`: The arithmetic operator.
    /// - `left`: Left operand.
    /// - `right`: Right operand.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing the computed scalar.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let x = Value::Real(1.5);
    /// let y = Value::Real(2.0);
    /// let line = 1;
    ///
    /// let result = Context::eval_scalar_op(BinaryOperator::Mul, &x, &y, line).unwrap();
    /// assert_eq!(result, Value::Real(3.0));
    /// ```
    pub fn eval_scalar_op(op: BinaryOperator,
                          left: &Value,
                          right: &Value,
                          line: usize)
                          -> EvalResult<Value> {
        use BinaryOperator::{Add, Div, Mul, Sub};
        use Value::{Complex, Integer, Real};

        match (&left, &right) {
            (Complex(_), _) | (_, Complex(_)) => {
                let (left, right) = left.clone().promote_to_complex(right, line)?;
                let left = left.as_complex(line)?;
                let right = right.as_complex(line)?;

                Ok(Complex(match op {
                               Add => left + right,
                               Sub => left - right,
                               Mul => left * right,
                               Div => {
                                   if right == ZERO {
                                       return Err(RuntimeError::DivisionByZero { line });
                                   }
                                   left / right
                               },
                               _ => unreachable!(),
                           }))
            },
            (Real(_), _) | (_, Real(_)) => {
                let (left, right) = left.clone().promote_to_real(right, line)?;
                let left = left.as_real(line)?;
                let right = right.as_real(line)?;

                Ok(Real(match op {
                            Add => left + right,
                            Sub => left - right,
                            Mul => left * right,
                            Div => {
                                if right == 0.0 {
                                    return Err(RuntimeError::DivisionByZero { line });
                                }
                                left / right
                            },
                            _ => unreachable!(),
                        }))
            },
            (Integer(a), Integer(b)) => match op {
                Add => Ok(Integer(a + b)),
                Sub => Ok(Integer(a - b)),
                Mul => Ok(Integer(a * b)),
                Div => {
                    if *b == 0 {
                        Err(RuntimeError::DivisionByZero { line })
                    } else {
                        Ok(Integer(a / b))
                    }
                },
                _ => unreachable!(),
            },
            _ => {
                Err(RuntimeError::TypeError { details: format!("Invalid scalar operands: {left} {op} {right}"),
                                              line })
            },
        }
    }
}
