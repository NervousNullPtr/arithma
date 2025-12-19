use crate::{
    ast::BinaryOperator,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
};

impl Context {
    /// Evaluates a logical operation between two boolean values.
    ///
    /// The operands are converted to booleans using `as_bool`.
    /// Supported operators are logical AND, XOR and OR.
    ///
    /// # Parameters
    /// - `op`: The logical operator.
    /// - `left`: Left operand.
    /// - `right`: Right operand.
    /// - `line`: Line number for error reporting.
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
    /// let context = Context::new();
    /// let a = Value::Bool(true);
    /// let b = Value::Bool(false);
    ///
    /// let result = context.eval_logic(BinaryOperator::Xor, &a, &b, 1);
    /// assert_eq!(result.unwrap(), Value::Bool(true));
    /// ```
    pub fn eval_logic(&self,
                      op: BinaryOperator,
                      left: &Value,
                      right: &Value,
                      line: usize)
                      -> EvalResult<Value> {
        use BinaryOperator::{And, Or, Xor};

        match op {
            And => Ok(Value::Bool(left.as_bool(line)? && right.as_bool(line)?)),
            Xor => Ok(Value::Bool(left.as_bool(line)? ^ right.as_bool(line)?)),
            Or => Ok(Value::Bool(left.as_bool(line)? || right.as_bool(line)?)),
            _ => unreachable!(),
        }
    }
}
