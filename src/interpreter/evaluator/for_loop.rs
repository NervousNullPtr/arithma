use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Expr, ForExprContext},
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
};

impl Context {
    /// Evaluates a `for` expression.
    ///
    /// A `for` expression binds a loop variable and repeatedly evaluates the
    /// loop body. Two forms are supported:
    ///
    /// 1. **Range form:** `for i = start .. end { body }` or exclusive upper
    ///    bound when `inclusive` is false. Both bounds must evaluate to
    ///    integers.
    ///
    /// 2. **Iterable form:** `for x in array { body }` The iterable must
    ///    evaluate to an array, and each element is bound to the loop variable
    ///    in turn.
    ///
    /// The loop variable cannot shadow an existing variable or a function
    /// binding. During iteration it becomes a forbidden variable,
    /// preventing assignments to it.
    ///
    /// The last evaluated body value is returned. If the loop executes zero
    /// times, the result is `None`.
    ///
    /// # Parameters
    /// - `context`: Loop header, including variable, bounds or iterable, and
    ///   body.
    /// - `bindings`: Optional parameter bindings for function calls.
    /// - `forbidden_vars`: Variables that may not be written inside the loop.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// The last yielded value from the loop body, or `None` if the loop did not
    /// run.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::*,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// // for i = 1..=3 { i }
    /// let for_expr =
    ///     Expr::ForExpr { context: ForExprContext { var:       "i".into(),
    ///                                               start:     Box::new(Expr::Literal { value:
    ///                                                                                       1.into(),
    ///                                                                                   line:  1, }),
    ///                                               end:
    ///                                                   Some(Box::new(Expr::Literal { value: 3.into(),
    ///                                                                                 line:  1, })),
    ///                                               inclusive: true,
    ///                                               body:
    ///                                                   Box::new(Expr::Variable { name: "i".into(),
    ///                                                                             line: 1, }), },
    ///                     line:    1, };
    ///
    /// let result = context.eval_for(&if let Expr::ForExpr { context, .. } = for_expr {
    ///                                   context
    ///                               } else {
    ///                                   unreachable!()
    ///                               },
    ///                               None,
    ///                               &HashSet::new(),
    ///                               1)
    ///                     .unwrap();
    ///
    /// assert_eq!(result, Some(Value::Integer(3)));
    /// ```
    pub fn eval_for(&mut self,
                    context: &ForExprContext,
                    bindings: Option<&HashMap<String, Value>>,
                    forbidden_vars: &HashSet<String>,
                    line: usize)
                    -> EvalResult<Option<Value>> {
        let shadowed = bindings.map_or_else(|| self.get_variable(&context.var).is_some(),
                                            |b| {
                                                self.get_variable(&context.var).is_some()
                                                || b.contains_key(&context.var)
                                            });
        if shadowed {
            return Err(RuntimeError::VariableShadowing { name: context.var.clone(),
                                                         line });
        }

        let mut new_forbidden = forbidden_vars.clone();
        new_forbidden.insert(context.var.clone());

        let mut eval_expr = |expr: &Expr| -> EvalResult<Value> {
            self.eval(expr, &new_forbidden, bindings)?
                .ok_or(RuntimeError::MissingValue { line })
        };

        let mut last_value = None;

        if let Some(end_expr) = &context.end {
            let start_value = (eval_expr(&context.start)?).value_to_i64(line)?;
            let end_value = (eval_expr(end_expr)?).value_to_i64(line)?;

            if start_value > end_value {
                return Err(RuntimeError::InvalidLoopBounds { details: format!("For-loop lower bound {start_value} is greater than the upper bound {end_value}"),
                                                             line });
            }

            let range: Box<dyn Iterator<Item = i64>> = if context.inclusive {
                Box::new(start_value..=end_value)
            } else {
                Box::new(start_value..end_value)
            };

            for i in range {
                let mut inner_bindings =
                    bindings.map_or_else(HashMap::new, std::clone::Clone::clone);

                inner_bindings.insert(context.var.clone(), i.into());

                last_value = self.eval(&context.body, &new_forbidden, Some(&inner_bindings))?;
            }
        } else {
            let iterable = eval_expr(&context.start)?;
            if let Value::Array(arr) = iterable {
                for element in arr.iter() {
                    let mut inner_bindings =
                        bindings.map_or_else(HashMap::new, std::clone::Clone::clone);

                    inner_bindings.insert(context.var.clone(), element.clone());

                    last_value = self.eval(&context.body, &new_forbidden, Some(&inner_bindings))?;
                }
            } else {
                return Err(RuntimeError::TypeError {
                    details: "For-loop without a range must iterate over an array".to_string(),
                    line,
                });
            }
        }

        Ok(last_value)
    }
}
