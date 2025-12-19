use std::rc::Rc;

use crate::{
    ast::BinaryOperator,
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
};

impl Context {
    /// Applies an elementwise binary operation to one or two values.
    ///
    /// This function unifies all array binary evaluation paths:
    /// - Array with array
    /// - Array with scalar
    /// - Scalar with array
    /// - Scalar with scalar
    ///
    /// Nested arrays are handled recursively. Shape compatibility is checked
    /// when both sides are arrays at the same level. The specific
    /// elementwise scalar operation is supplied via the function parameter
    /// `f`.
    ///
    /// # Parameters
    /// - `op`: The operator being applied. Only needed for error messages.
    /// - `left`: Left-hand operand.
    /// - `right`: Right-hand operand.
    /// - `line`: Current line number for error reporting.
    /// - `f`: Elementwise scalar operation used when both operands are
    ///   non-array values.
    ///
    /// # Returns
    /// A `Value` containing either a scalar or an array reflecting the result.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let left = Value::Array(vec![Value::Integer(1), Value::Integer(2)].into());
    /// let right = Value::Array(vec![Value::Integer(10), Value::Integer(20)].into());
    ///
    /// let r = Context::map_array_binary(BinaryOperator::Add, &left, &right, 1, &|l, r| {
    ///             Context::eval_scalar_op(BinaryOperator::Add, l, r, 1)
    ///         }).unwrap();
    ///
    /// assert_eq!(r,
    ///            Value::Array(vec![Value::Integer(11), Value::Integer(22)].into()));
    /// ```
    pub fn map_array_binary<F>(op: BinaryOperator,
                               left: &Value,
                               right: &Value,
                               line: usize,
                               f: &F)
                               -> EvalResult<Value>
        where F: Fn(&Value, &Value) -> EvalResult<Value>
    {
        match (left, right) {
            // Array with array
            (Value::Array(larr), Value::Array(rarr)) => {
                if larr.len() != rarr.len() {
                    return Err(RuntimeError::TypeError { details: format!("Cannot apply {op} to arrays of different lengths: {} vs {}",
                                                                          larr.len(),
                                                                          rarr.len()),
                                                         line });
                }

                let mut out = Vec::with_capacity(larr.len());
                for (l, r) in larr.iter().zip(rarr.iter()) {
                    let v = Self::map_array_binary(op, l, r, line, f)?;
                    out.push(v);
                }
                Ok(Value::Array(out.into()))
            },

            // Array with scalar
            (Value::Array(arr), scalar) => {
                let mut out = Vec::with_capacity(arr.len());
                for l in arr.iter() {
                    let v = Self::map_array_binary(op, l, scalar, line, f)?;
                    out.push(v);
                }
                Ok(Value::Array(out.into()))
            },

            // Scalar with array
            (scalar, Value::Array(arr)) => {
                let mut out = Vec::with_capacity(arr.len());
                for r in arr.iter() {
                    let v = Self::map_array_binary(op, scalar, r, line, f)?;
                    out.push(v);
                }
                Ok(Value::Array(out.into()))
            },

            // Scalar with scalar
            (l, r) => f(l, r),
        }
    }
    /// Evaluates an elementwise operation of the form `Array <op> Scalar` or
    /// `Scalar <op> Array`.
    ///
    /// Delegates all structural work to `map_array_binary`. Only the scalar
    /// operator logic is supplied. Nested arrays are handled recursively.
    ///
    /// # Parameters
    /// - `op`: Binary operator.
    /// - `array`: Array operand.
    /// - `scalar`: Scalar operand.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// A `Value::Array` containing the elementwise result.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let array = vec![Value::Integer(1), Value::Integer(2)];
    /// let scalar = Value::Integer(5);
    ///
    /// let r = Context::eval_array_scalar(BinaryOperator::Add, &array, &scalar, 1).unwrap();
    ///
    /// assert_eq!(r,
    ///            Value::Array(vec![Value::Integer(6), Value::Integer(7)].into()));
    /// ```
    pub fn eval_array_scalar(op: BinaryOperator,
                             array: &[Value],
                             scalar: &Value,
                             line: usize)
                             -> EvalResult<Value> {
        Self::map_array_binary(op,
                               &Value::Array(Rc::new(array.to_vec())),
                               scalar,
                               line,
                               &|l, r| Self::eval_scalar_op(op, l, r, line))
    }
    /// Evaluates an elementwise operation of the form `Array <op> Array`.
    ///
    /// Arrays must have the same shape at each recursion level. All structural
    /// work and recursion is performed by `map_array_binary`. Only the scalar
    /// operator logic is supplied.
    ///
    /// # Parameters
    /// - `op`: Binary operator.
    /// - `left`: Left operand array.
    /// - `right`: Right operand array.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// A `Value::Array` whose structure matches the inputs.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let left = vec![Value::Integer(1), Value::Integer(2)];
    /// let right = vec![Value::Integer(10), Value::Integer(20)];
    ///
    /// let r = Context::eval_array_array(BinaryOperator::Mul, &left, &right, 1).unwrap();
    ///
    /// assert_eq!(r,
    ///            Value::Array(vec![Value::Integer(10), Value::Integer(40)].into()));
    /// ```
    pub fn eval_array_array(op: BinaryOperator,
                            left: &[Value],
                            right: &[Value],
                            line: usize)
                            -> EvalResult<Value> {
        Self::map_array_binary(op,
                               &Value::Array(left.to_vec().into()),
                               &Value::Array(right.to_vec().into()),
                               line,
                               &|l, r| Self::eval_scalar_op(op, l, r, line))
    }
}
