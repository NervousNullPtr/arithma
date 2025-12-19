use crate::{
    ast::BinaryOperator::{self},
    interpreter::{
        evaluator::{
            core::{Context, EvalResult},
            utils::{is_close, strict_eq},
        },
        value::core::Value::{self},
    },
};

/// Maps an equality-style operator and a boolean equality result
/// to the final boolean value.
///
/// Used by both `eval_comparison` and `eval_approx` to invert the
/// result for the negated variants (`NotEqual`, `NotApproxEqual`).
///
/// This function does not perform any numeric work itself.
#[must_use]
pub fn equality_op_result(op: BinaryOperator, is_equal: bool) -> bool {
    match op {
        BinaryOperator::Equal | BinaryOperator::ApproxEqual => is_equal,
        BinaryOperator::NotEqual | BinaryOperator::NotApproxEqual => !is_equal,
        _ => unreachable!("equality_op_result used with non equality operator"),
    }
}

impl Context {
    /// Evaluates a comparison of the form `Value <Operator> Value`.
    ///
    /// This function handles equality and relational comparisons.
    /// For `Equal` and `NotEqual`, values are compared using strict structural
    /// equality. For relational operators, both operands are promoted to
    /// real numbers when needed.
    ///
    /// # Parameters
    /// - `op`: The comparison operator.
    /// - `left`: The left-hand value.
    /// - `right`: The right-hand value.
    /// - `line`: Current line number used for error reporting.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing a boolean result.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let a = Value::Real(3.0);
    /// let b = Value::Real(5.0);
    /// let line = 1;
    ///
    /// let result = Context::eval_comparison(BinaryOperator::Less, &a, &b, line);
    ///
    /// assert_eq!(result.unwrap(), Value::Bool(true));
    /// ```
    pub fn eval_comparison(op: BinaryOperator,
                           left: &Value,
                           right: &Value,
                           line: usize)
                           -> EvalResult<Value> {
        Ok(Value::Bool(match op {
                           BinaryOperator::Equal | BinaryOperator::NotEqual => {
                               let equality = strict_eq(left, right, line)?;
                               equality_op_result(op, equality)
                           },

                           BinaryOperator::Less
                           | BinaryOperator::Greater
                           | BinaryOperator::LessEqual
                           | BinaryOperator::GreaterEqual => {
                               let (left, right) = left.clone().promote_to_real(right, line)?;
                               let left = left.as_real(line)?;
                               let right = right.as_real(line)?;

                               match op {
                                   BinaryOperator::Less => left < right,
                                   BinaryOperator::Greater => left > right,
                                   BinaryOperator::LessEqual => left <= right,
                                   BinaryOperator::GreaterEqual => left >= right,
                                   _ => unreachable!(),
                               }
                           },

                           _ => unreachable!(),
                       }))
    }
    /// Evaluates an approximate comparison of the form `Value ≈ Value` or its
    /// negation.
    ///
    /// This function checks whether two values are approximately equal within
    /// given absolute and relative tolerances. Integer, real and complex
    /// values are supported. Type promotion is applied so that both
    /// operands are compared in a compatible form.
    ///
    /// The comparison is performed using `is_close`, which computes the
    /// absolute difference between the values and compares it to the larger
    /// of `abs_tol` and `rel_tol * max_norm`, where `max_norm` is the
    /// maximum magnitude of the promoted operands.
    ///
    /// # Parameters
    /// - `left`: The left-hand value.
    /// - `right`: The right-hand value.
    /// - `line`: Current line number for error reporting.
    /// - `op`: The operator (`ApproxEqual` or `NotApproxEqual`).
    /// - `rel_tol`: Relative tolerance.
    /// - `abs_tol`: Absolute tolerance.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing a boolean.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let a = Value::Real(1.000001);
    /// let b = Value::Real(1.0);
    /// let line = 1;
    /// let rel = 1e-6;
    /// let abs = 1e-12;
    ///
    /// let result = Context::eval_approx(&a, &b, line, BinaryOperator::ApproxEqual, rel, abs);
    ///
    /// assert_eq!(result.unwrap(), Value::Bool(true));
    /// ```
    pub fn eval_approx(left: &Value,
                       right: &Value,
                       line: usize,
                       op: BinaryOperator,
                       rel_tol: f64,
                       abs_tol: f64)
                       -> EvalResult<Value> {
        let is_equal = is_close(left, right, abs_tol, rel_tol, line)?;

        Ok(Value::Bool(equality_op_result(op, is_equal)))
    }
}
