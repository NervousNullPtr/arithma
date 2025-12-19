use std::{collections::HashSet, rc::Rc};

use crate::{
    ast::BinaryOperator,
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::{core::Value, set_value::SetValue},
    },
};

impl Context {
    /// Evaluates a set operation on two sets.
    ///
    /// Supported operators map to standard set operations:
    /// - `Add` produces the union.
    /// - `Sub` produces the difference.
    /// - `Intersection` produces the intersection.
    /// - `SymmDifference` produces the symmetric difference.
    ///
    /// Any other operator results in a type error.
    ///
    /// # Parameters
    /// - `op`: The set operator.
    /// - `left`: Left-hand set.
    /// - `right`: Right-hand set.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing the resulting set.
    ///
    /// # Example
    /// ```
    /// use std::{collections::HashSet, rc::Rc};
    ///
    /// use arithma::{
    ///     ast::BinaryOperator,
    ///     interpreter::{
    ///         evaluator::core::Context,
    ///         value::{core::Value, set_value::SetValue},
    ///     },
    /// };
    ///
    /// let a: HashSet<SetValue> = [SetValue::Integer(1), SetValue::Integer(2)].into_iter()
    ///                                                                        .collect();
    /// let b: HashSet<SetValue> = [SetValue::Integer(2), SetValue::Integer(3)].into_iter()
    ///                                                                        .collect();
    ///
    /// let result = Context::eval_set_op(BinaryOperator::Add, &a, &b, 1).unwrap();
    ///
    /// assert_eq!(result,
    ///            Value::Set(Rc::new([SetValue::Integer(1),
    ///                                SetValue::Integer(2),
    ///                                SetValue::Integer(3)].into_iter()
    ///                                                     .collect())));
    /// ```
    pub fn eval_set_op(op: BinaryOperator,
                       left: &HashSet<SetValue>,
                       right: &HashSet<SetValue>,
                       line: usize)
                       -> EvalResult<Value> {
        match op {
            BinaryOperator::Add => Ok(Value::Set(Rc::new(left.clone()
                                                             .union(right)
                                                             .cloned()
                                                             .collect()))),
            BinaryOperator::Sub => Ok(Value::Set(Rc::new(left.clone()
                                                             .difference(right)
                                                             .cloned()
                                                             .collect()))),
            BinaryOperator::Intersection => Ok(Value::Set(Rc::new(left.clone()
                                                                      .intersection(right)
                                                                      .cloned()
                                                                      .collect()))),
            BinaryOperator::SymmDifference => Ok(Value::Set(Rc::new(left.clone()
                                                                        .symmetric_difference(right)
                                                                        .cloned()
                                                                        .collect()))),
            _ => Err(RuntimeError::TypeError { details: format!("Cannot use {op} on sets"),
                                               line }),
        }
    }
}
