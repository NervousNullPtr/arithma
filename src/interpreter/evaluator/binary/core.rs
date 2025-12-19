use crate::{
    ast::BinaryOperator,
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
};

impl Context {
    /// Evaluates a binary operation between two values.
    ///
    /// This function routes the operation to specialized handlers depending on
    /// the operator and operand types. Arithmetic operations choose between
    /// array, scalar or set evaluation. Modulo supports integers and reals with
    /// promotion. Power calls `eval_pow`.
    /// Relational and equality operators use `eval_comparison`.
    /// Approximate comparisons use `eval_approx` with explicit or context
    /// tolerances.
    /// Logical operators call `eval_logic`.
    /// Matrix multiplication delegates to `eval_matmul`.
    ///
    /// # Parameters
    /// - `op`: The operator.
    /// - `left`: Left operand.
    /// - `right`: Right operand.
    /// - `line`: Line number for error reporting.
    /// - `rel_tolerance`: Optional relative tolerance.
    /// - `abs_tolerance`: Optional absolute tolerance.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing the evaluated result.
    ///
    /// # Example
    /// ```
    /// use std::rc::Rc;
    ///
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let context = Context::new();
    /// let left = Value::Integer(3);
    /// let right = Value::Integer(4);
    /// let line = 1;
    ///
    /// let result = context.eval_binary(BinaryOperator::Add, &left, &right, line, None, None);
    /// assert_eq!(result.unwrap(), Value::Integer(7));
    /// ```
    pub fn eval_binary(&self,
                       op: BinaryOperator,
                       left: &Value,
                       right: &Value,
                       line: usize,
                       rel_tolerance: Option<f64>,
                       abs_tolerance: Option<f64>)
                       -> EvalResult<Value> {
        use BinaryOperator::{
            Add, And, ApproxEqual, Div, Equal, Greater, GreaterEqual, Intersection, Less,
            LessEqual, Mod, Mul, NotApproxEqual, NotEqual, Or, Pow, Sub, SymmDifference, Xor,
        };
        use Value::{Array, Integer, Real, Set};

        match op {
            Add | Sub | Mul | Div => match (&left, &right) {
                (Array(a), Array(b)) => Self::eval_array_array(op, a, b, line),
                (Array(a), b) => Self::eval_array_scalar(op, a, b, line),
                (a, Array(b)) => Self::eval_array_scalar(op, b, a, line),
                (Set(a), Set(b)) => Self::eval_set_op(op, a, b, line),
                _ => Self::eval_scalar_op(op, left, right, line),
            },

            Mod => match (&left, &right) {
                (Integer(a), Integer(b)) => Ok(Integer(a % b)),
                (Real(_), _) | (_, Real(_)) => {
                    let (l, r) = left.clone().promote_to_real(right, line)?;
                    Ok(Real(l.as_real(line)? % r.as_real(line)?))
                },
                _ => {
                    Err(RuntimeError::TypeError { details: format!("Cannot use {op} on {left} and {right}"),
                                                  line })
                },
            },

            Pow => Self::eval_pow(left, right, line),

            Less | Greater | LessEqual | GreaterEqual | Equal | NotEqual => {
                Self::eval_comparison(op, left, right, line)
            },

            ApproxEqual | NotApproxEqual => {
                let rel_tol = rel_tolerance.unwrap_or(self.rel_tolerance);
                let abs_tol = abs_tolerance.unwrap_or(self.abs_tolerance);
                Self::eval_approx(left, right, line, op, rel_tol, abs_tol)
            },

            Intersection | SymmDifference => match (&left, &right) {
                (Set(a), Set(b)) => Self::eval_set_op(op, a, b, line),
                _ => {
                    Err(RuntimeError::TypeError { details: format!("Cannot use {op} on {left} and {right}"),
                                                  line })
                },
            },

            And | Xor | Or => self.eval_logic(op, left, right, line),

            BinaryOperator::MatMul => Self::eval_matmul(left, right, line),
        }
    }
}
