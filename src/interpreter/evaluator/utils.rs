use std::collections::{HashMap, HashSet};

use crate::{
    ast::{BinaryOperator, Expr, LiteralValue, Statement, UnaryOperator},
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::{complex::ComplexNumber, core::Value},
    },
    util::num::{self, i64_to_f64_checked, usize_to_f64_checked},
};

/// Reserved identifiers that do not fall into any other category such as
/// complex number units.
pub const EXTRA_RESERVED: &[&str] = &["i", "j"];

pub struct ScopeGuard {
    context_pointer: *mut Context,
}

impl Drop for ScopeGuard {
    fn drop(&mut self) {
        unsafe { (*self.context_pointer).pop_scope() };
    }
}

impl Context {
    /// Evaluates a subexpression and ensures that it produces a value.
    ///
    /// Many evaluation paths require the same sequence:
    /// evaluate the expression, check for `None`, convert to a `Value`,
    /// and report a `MissingValue` error when the expression yields nothing.
    ///
    /// This helper centralizes that behavior so that unary, binary,
    /// and function-call logic remain simple and consistent.
    ///
    /// # Parameters
    /// - `expr`: Expression to evaluate.
    /// - `forbidden`: Variables that cannot be assigned in this context.
    /// - `bindings`: Optional parameter bindings for function bodies.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// The evaluated `Value`.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::Expr,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut ctx = Context::new();
    /// let expr = Expr::Literal { value: 10.into(),
    ///                            line:  1, };
    ///
    /// let v = ctx.eval_child(&expr, &HashSet::new(), None, 1).unwrap();
    /// assert_eq!(v, Value::Integer(10));
    /// ```
    pub fn eval_child(&mut self,
                      expr: &Expr,
                      forbidden: &std::collections::HashSet<String>,
                      bindings: Option<&std::collections::HashMap<String, Value>>,
                      line: usize)
                      -> EvalResult<Value> {
        self.eval(expr, forbidden, bindings)?
            .ok_or(RuntimeError::MissingValue { line })
    }
    /// Evaluates a literal expression.
    ///
    /// Converts the literal value directly into a `Value` and returns it.
    /// Literals never produce errors.
    ///
    /// # Parameters
    /// - `value`: Literal to convert.
    ///
    /// # Returns
    /// `Some(Value)` wrapping the literal.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::LiteralValue,
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let value = Context::eval_literal(&7.into()).unwrap();
    /// assert_eq!(value, Some(Value::Integer(7)));
    /// ```
    #[allow(clippy::unnecessary_wraps)]
    pub fn eval_literal(value: &LiteralValue) -> EvalResult<Option<Value>> {
        Ok(Some(Value::from(value)))
    }

    /// Looks up a variable by name.
    ///
    /// Variable lookup checks, in order:
    /// 1. Local function bindings (when evaluating a function body).
    /// 2. Variables in the current scope stack.
    ///
    /// If the variable is not found, an `UnknownVariable` error is returned.
    ///
    /// # Parameters
    /// - `name`: Variable name.
    /// - `line`: Line number for error reporting.
    /// - `bindings`: Optional parameter bindings for user-defined functions.
    ///
    /// # Returns
    /// The variable value, if found.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let mut ctx = Context::new();
    /// ctx.define_local("x", Value::Integer(10));
    ///
    /// let v = ctx.eval_variable(&"x".to_string(), 1, None).unwrap();
    /// assert_eq!(v, Some(Value::Integer(10)));
    /// ```
    pub fn eval_variable(&self,
                         name: &String,
                         line: usize,
                         bindings: Option<&HashMap<String, Value>>)
                         -> EvalResult<Option<Value>> {
        if let Some(b) = bindings
           && let Some(value) = b.get(name)
        {
            return Ok(Some(value.clone()));
        }
        if let Some(value) = self.get_variable(name) {
            return Ok(Some(value.clone()));
        }
        Err(RuntimeError::UnknownVariable { name: name.to_owned(),
                                            line })
    }

    /// Evaluates a unary operator applied to a subexpression.
    ///
    /// Uses `eval_child` to obtain the operand value, then applies the
    /// numeric or boolean operator using `Context::eval_unary`.
    ///
    /// # Parameters
    /// - `op`: The unary operator.
    /// - `expr`: Operand expression.
    /// - `line`: Line number.
    /// - `forbidden_vars`: Variables that cannot be assigned here.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// The computed value.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue, UnaryOperator},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    /// let e = Expr::Literal { value: 5.into(),
    ///                         line:  1, };
    ///
    /// let r = context.eval_unary_op(UnaryOperator::Negate, &e, 1, &HashSet::new(), None)
    ///                .unwrap();
    /// assert_eq!(r, Some(Value::Integer(-5)));
    /// ```
    pub fn eval_unary_op(&mut self,
                         op: UnaryOperator,
                         expr: &Expr,
                         line: usize,
                         forbidden_vars: &HashSet<String>,
                         bindings: Option<&HashMap<String, Value>>)
                         -> EvalResult<Option<Value>> {
        let val = self.eval_child(expr, forbidden_vars, bindings, line)?;
        Ok(Some(Self::eval_unary(op, &val, line)?))
    }

    /// Evaluates a binary operator applied to two expressions.
    ///
    /// Both operands are evaluated using `eval_child`, ensuring consistent
    /// handling of missing values. The resulting `Value`s are then passed to
    /// `Context::eval_binary` together with any user-specified tolerances.
    ///
    /// # Parameters
    /// - `left`: Left operand.
    /// - `op`: Operator.
    /// - `right`: Right operand.
    /// - `line`: Line number.
    /// - `forbidden_vars`: Variables forbidden in this context.
    /// - `rel_tolerance`: Optional relative tolerance override.
    /// - `abs_tolerance`: Optional absolute tolerance override.
    /// - `bindings`: Function-call bindings when inside a user-defined
    ///   function.
    ///
    /// # Returns
    /// The evaluated result.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::{BinaryOperator, Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut ctx = Context::new();
    /// let l = Expr::Literal { value: 2.into(),
    ///                         line:  1, };
    /// let r = Expr::Literal { value: 3.into(),
    ///                         line:  1, };
    ///
    /// let v = ctx.eval_binary_op(&l,
    ///                            BinaryOperator::Add,
    ///                            &r,
    ///                            1,
    ///                            &HashSet::new(),
    ///                            None,
    ///                            None,
    ///                            None)
    ///            .unwrap();
    ///
    /// assert_eq!(v, Some(Value::Integer(5)));
    /// ```
    #[allow(clippy::too_many_arguments)]
    pub fn eval_binary_op(&mut self,
                          left: &Expr,
                          op: BinaryOperator,
                          right: &Expr,
                          line: usize,
                          forbidden_vars: &HashSet<String>,
                          rel_tolerance: Option<f64>,
                          abs_tolerance: Option<f64>,
                          bindings: Option<&HashMap<String, Value>>)
                          -> EvalResult<Option<Value>> {
        let lval = self.eval_child(left, forbidden_vars, bindings, line)?;
        let rval = self.eval_child(right, forbidden_vars, bindings, line)?;

        Ok(Some(self.eval_binary(op,
                                 &lval,
                                 &rval,
                                 line,
                                 rel_tolerance,
                                 abs_tolerance)?))
    }

    /// Evaluates a function call expression.
    ///
    /// Argument expressions are each evaluated using `eval_child` so that
    /// missing-value handling is consistent. After collecting arguments the
    /// call is dispatched to either a builtin or a user-defined function.
    ///
    /// # Parameters
    /// - `name`: Function name.
    /// - `arguments`: Expression arguments.
    /// - `line`: Line number.
    /// - `forbidden_vars`: Variables disallowed inside the call.
    /// - `bindings`: Parameter bindings if inside a user-defined function.
    ///
    /// # Returns
    /// Result of the function.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// // Define a user function: f(x) = x + 1
    /// context.functions.insert(
    ///     "f".into(),
    ///     arithma::ast::FunctionDef {
    ///         name: "f".into(),
    ///         params: vec!["x".into()],
    ///         body: Expr::BinaryOp {
    ///             left: Box::new(Expr::Variable { name: "x".into(), line: 1 }),
    ///             op: arithma::ast::BinaryOperator::Add,
    ///             right: Box::new(Expr::Literal { value: 1.into(), line: 1 }),
    ///             line: 1,
    ///             rel_tolerance: None,
    ///             abs_tolerance: None
    ///         },
    ///         line: 1
    ///     }
    /// );
    ///
    /// let arg = Expr::Literal { value: 10.into(),
    ///                           line:  1, };
    ///
    /// let result = context.eval_function_call("f", &vec![arg], 1, &HashSet::new(), None)
    ///                     .unwrap();
    ///
    /// assert_eq!(result, 11.into());
    /// ```
    pub fn eval_function_call(&mut self,
                              name: &str,
                              arguments: &Vec<Expr>,
                              line: usize,
                              forbidden_vars: &HashSet<String>,
                              bindings: Option<&HashMap<String, Value>>)
                              -> EvalResult<Value> {
        let mut args = Vec::with_capacity(arguments.len());

        for expr in arguments {
            args.push(self.eval_child(expr, forbidden_vars, bindings, line)?);
        }

        self.eval_function(name, args, forbidden_vars, line)
    }

    /// Evaluates an absolute value expression.
    ///
    /// The operand expression is evaluated first.
    /// If it produces no value, a `MissingValue` error is returned.
    /// The resulting value must support absolute value, which is delegated to
    /// `Value::abs(line)`.
    ///
    /// # Parameters
    /// - `expr`: Expression whose absolute value is computed.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// `Some(Value)` containing the absolute value.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// let e = Expr::Literal { value: (-5).into(),
    ///                         line:  1, };
    /// let r = context.eval_abs(&e, 1, &HashSet::new(), None).unwrap();
    ///
    /// assert_eq!(r, Some(Value::Integer(5)));
    /// ```
    pub fn eval_abs(&mut self,
                    expr: &Expr,
                    line: usize,
                    forbidden_vars: &HashSet<String>,
                    bindings: Option<&HashMap<String, Value>>)
                    -> EvalResult<Option<Value>> {
        Ok(Some(self.eval(expr, forbidden_vars, bindings)?
                    .ok_or(RuntimeError::MissingValue { line })?
                    .abs(line)?))
    }

    /// Evaluates an `if` expression.
    ///
    /// The condition is evaluated first and converted to a boolean.
    /// If the condition is true, the `then` branch is evaluated.
    /// If false, the `else` branch is evaluated when provided.
    /// If false and no `else` branch exists, the expression returns `None`.
    ///
    /// Missing operand values produce a `MissingValue` error.
    ///
    /// # Parameters
    /// - `condition`: Condition expression.
    /// - `then_branch`: Expression evaluated when the condition is true.
    /// - `else_branch`: Optional fallback expression.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// The value of the selected branch or `None` if no branch is taken.
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// let condition = Expr::Literal { value: true.into(),
    ///                                 line:  1, };
    /// let then = Expr::Literal { value: 1.into(),
    ///                            line:  1, };
    /// let elseblock = Expr::Literal { value: 2.into(),
    ///                                 line:  1, };
    ///
    /// let r = context.eval_if_expr(&condition,
    ///                              &then,
    ///                              Some(&elseblock),
    ///                              1,
    ///                              &HashSet::new(),
    ///                              None)
    ///                .unwrap();
    ///
    /// assert_eq!(r, Some(Value::Integer(1)));
    /// ```
    pub fn eval_if_expr(&mut self,
                        condition: &Expr,
                        then_branch: &Expr,
                        else_branch: Option<&Expr>,
                        line: usize,
                        forbidden_vars: &HashSet<String>,
                        bindings: Option<&HashMap<String, Value>>)
                        -> EvalResult<Option<Value>> {
        let cond = self.eval(condition, forbidden_vars, bindings)?
                       .ok_or(RuntimeError::MissingValue { line })?
                       .as_bool(line)?;

        let result = if cond {
            self.eval(then_branch, forbidden_vars, bindings)?
        } else if let Some(else_expr) = else_branch {
            self.eval(else_expr, forbidden_vars, bindings)?
        } else {
            None
        };

        Ok(result)
    }

    /// Evaluates a sequence of statements as a block.
    ///
    /// A new local scope is pushed before execution and removed afterward.
    /// Each statement is evaluated in order.
    /// The value of the final statement is returned, or `None` if the block is
    /// empty.
    ///
    /// # Parameters
    /// - `statements`: Statements inside the block.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional parameter bindings for function bodies.
    ///
    /// # Returns
    /// The value of the last executed statement or `None`.
    ///
    /// # Example
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue, Statement},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// // { x = 3; x }
    /// let statements = vec![Statement::VariableDeclaration { name:  "x".into(),
    ///                                                        value: Expr::Literal { value: 3.into(),
    ///                                                                               line:  1, },
    ///                                                        line:  1, },
    ///                       Statement::Expression { expr: Expr::Variable { name: "x".into(),
    ///                                                                      line: 1, },
    ///                                               line: 1, }];
    ///
    /// let r = context.eval_block(&statements, &HashSet::new(), None)
    ///                .unwrap();
    /// assert_eq!(r, Some(Value::Integer(3)));
    /// ```
    pub fn eval_block(&mut self,
                      statements: &Vec<Statement>,
                      forbidden_vars: &HashSet<String>,
                      bindings: Option<&HashMap<String, Value>>)
                      -> EvalResult<Option<Value>> {
        self.push_scope();
        let mut last = None;

        for stmt in statements {
            last = self.eval_statement(stmt, bindings, forbidden_vars)?;
        }

        self.pop_scope();
        Ok(last)
    }

    /// Evaluates a sequence of top-level statements.
    ///
    /// Each statement is executed in order with no additional forbiddance rules
    /// and no function-parameter bindings.
    /// The value of the final statement is returned, or `None` if the list is
    /// empty.
    ///
    /// # Parameters
    /// - `statements`: Slice of top-level statements.
    ///
    /// # Returns
    /// The last evaluated value or `None`.
    ///
    /// # Example
    /// ```
    /// use arithma::{
    ///     ast::{Expr, LiteralValue, Statement},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// let statements = vec![Statement::VariableDeclaration { name:  "a".to_string(),
    ///                                                        value: Expr::Literal { value: 10.into(),
    ///                                                                               line:  1, },
    ///                                                        line:  1, },
    ///                       Statement::Expression { expr: Expr::Variable { name: "a".into(),
    ///                                                                      line: 1, },
    ///                                               line: 1, }];
    ///
    /// let r = context.eval_toplevel(&statements).unwrap();
    /// assert_eq!(r, Some(Value::Integer(10)));
    /// ```
    pub fn eval_toplevel(&mut self, statements: &[Statement]) -> EvalResult<Option<Value>> {
        let mut last_val = None;
        for stmt in statements {
            last_val = self.eval_statement(stmt, None, &std::collections::HashSet::new())?;
        }
        Ok(last_val)
    }
    /// Evaluates a list of element expressions into concrete values.
    ///
    /// Each element expression is evaluated in order. If any expression does
    /// not yield a value, a `MissingValue` error is returned. This helper is
    /// used by literal evaluators such as arrays and sets.
    ///
    /// # Parameters
    /// - `elements`: Expressions to evaluate.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// A vector of fully evaluated `Value`s.
    pub fn eval_elements_to_values(&mut self,
                                   elements: &Vec<Expr>,
                                   line: usize,
                                   forbidden_vars: &HashSet<String>,
                                   bindings: Option<&HashMap<String, Value>>)
                                   -> EvalResult<Vec<Value>> {
        let mut values = Vec::with_capacity(elements.len());

        for element in elements {
            let value = self.eval(element, forbidden_vars, bindings)?
                            .ok_or(RuntimeError::MissingValue { line })?;
            values.push(value);
        }

        Ok(values)
    }
    /// Evaluates an array literal expression.
    ///
    /// Each element expression is evaluated in order.
    /// If an element does not yield a value, a `MissingValue` error is
    /// returned. The resulting elements are collected into a
    /// `Value::Array`.
    ///
    /// # Parameters
    /// - `elements`: Expressions forming the array.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be assigned within this
    ///   context.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// `Some(Value::Array)` with all evaluated elements.
    ///
    /// # Example
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut ctx = Context::new();
    ///
    /// let elements = vec![Expr::Literal { value: 1.into(),
    ///                                     line:  1, },
    ///                     Expr::Literal { value: 2.into(),
    ///                                     line:  1, },];
    ///
    /// let result = ctx.eval_array_literal(&elements, 1, &HashSet::new(), None)
    ///                 .unwrap();
    ///
    /// assert_eq!(result,
    ///            Some(Value::Array(vec![Value::Integer(1), Value::Integer(2)].into())));
    /// ```
    pub fn eval_array_literal(&mut self,
                              elements: &Vec<Expr>,
                              line: usize,
                              forbidden_vars: &HashSet<String>,
                              bindings: Option<&HashMap<String, Value>>)
                              -> EvalResult<Option<Value>> {
        let values = self.eval_elements_to_values(elements, line, forbidden_vars, bindings)?;

        Ok(Some(Value::Array(values.into())))
    }

    /// Evaluates a set literal expression.
    ///
    /// Each element is evaluated, converted into a `SetValue`, and inserted
    /// into a new set. If any element does not produce a value, a
    /// `MissingValue` error is returned. Duplicates are removed
    /// automatically by the `HashSet`.
    ///
    /// # Parameters
    /// - `elements`: Expressions forming the set.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// `Some(Value::Set)` containing all unique evaluated elements.
    ///
    /// # Example
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{
    ///         evaluator::core::Context,
    ///         value::{core::Value, set_value::SetValue},
    ///     },
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// let elements = vec![Expr::Literal { value: 1.into(),
    ///                                     line:  1, },
    ///                     Expr::Literal { value: 1.into(),
    ///                                     line:  1, },
    ///                     Expr::Literal { value: 2.into(),
    ///                                     line:  1, },];
    ///
    /// let result = context.eval_set_literal(&elements, 1, &HashSet::new(), None)
    ///                     .unwrap();
    ///
    /// let expected: HashSet<SetValue> = [SetValue::from(&Value::Integer(1)),
    ///                                    SetValue::from(&Value::Integer(2))].into_iter()
    ///                                                                       .collect();
    ///
    /// assert_eq!(result, Some(Value::Set(expected.into())));
    /// ```
    pub fn eval_set_literal(&mut self,
                            elements: &Vec<Expr>,
                            line: usize,
                            forbidden_vars: &HashSet<String>,
                            bindings: Option<&HashMap<String, Value>>)
                            -> EvalResult<Option<Value>> {
        use crate::interpreter::value::set_value::SetValue;

        let values = self.eval_elements_to_values(elements, line, forbidden_vars, bindings)?;

        let mut set = HashSet::with_capacity(values.len());

        for value in &values {
            set.insert(SetValue::from(value));
        }

        Ok(Some(Value::Set(set.into())))
    }

    /// Evaluates an array indexing expression.
    ///
    /// Both the array expression and index expression are evaluated first.
    /// The index must be an integer; otherwise a `TypeError` is returned.
    /// The array expression must evaluate to an array. If the index is out of
    /// bounds, an `IndexOutOfBounds` error is returned.
    ///
    /// # Parameters
    /// - `array`: Expression producing the array.
    /// - `index`: Expression producing the index.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// `Some(Value)` containing the array element at the given index.
    ///
    /// # Panics
    /// This function **panics only if** `Value::as_vec(line)` fails internally
    /// due to an inconsistent `Value` variant (i.e., a non-array variant
    /// claiming to be an array). Under correct interpreter behavior this
    /// never occurs.
    ///
    /// # Example
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// let array = Expr::ArrayLiteral { elements: vec![Expr::Literal { value: 10.into(),
    ///                                                                 line:  1, },
    ///                                                 Expr::Literal { value: 20.into(),
    ///                                                                 line:  1, },],
    ///                                  line:     1, };
    ///
    /// let index = Expr::Literal { value: 1.into(),
    ///                             line:  1, };
    ///
    /// let result = context.eval_array_index(&array, &index, 1, &HashSet::new(), None)
    ///                     .unwrap();
    ///
    /// assert_eq!(result, Some(Value::Integer(20)));
    /// ```
    pub fn eval_array_index(&mut self,
                            array: &Expr,
                            index: &Expr,
                            line: usize,
                            forbidden_vars: &HashSet<String>,
                            bindings: Option<&HashMap<String, Value>>)
                            -> EvalResult<Option<Value>> {
        let (array_value, index_value) = {
            let array_val = self.eval(array, forbidden_vars, bindings)?
                                .ok_or(RuntimeError::MissingValue { line })?;
            let index_val = self.eval(index, forbidden_vars, bindings)?
                                .ok_or(RuntimeError::MissingValue { line })?;
            (array_val, index_val)
        };

        if !index_value.is_integer() {
            return Err(RuntimeError::TypeError { details:
                                                     "Array index must be an integer".to_string(),
                                                 line });
        }
        let index = index_value.as_integer(line)?;

        if !array_value.is_array() {
            return Err(RuntimeError::TypeError { details:
                                                     "Tried to index non-array value".to_string(),
                                                 line });
        }

        let arr = array_value.as_vec(line).unwrap();

        let index = num::i64_to_usize_checked(index, line)?;

        arr.get(index)
           .cloned()
           .ok_or_else(|| RuntimeError::IndexOutOfBounds { max: arr.len().saturating_sub(1),
                                                           found: index,
                                                           line })
           .map(Some)
    }

    /// Evaluates the Euclidean norm of an array.
    ///
    /// The operand expression must evaluate to an array.
    /// - An empty array has norm `0.0`.
    /// - Arrays of integers are summed using checked integer arithmetic to
    ///   avoid overflow, then converted to floating point.
    /// - Mixed or non-integer numeric values are promoted to `f64` and summed
    ///   normally.
    ///
    /// Non-array values produce a `TypeError`.
    ///
    /// # Parameters
    /// - `array`: Expression producing the array.
    /// - `line`: Line number for error reporting.
    /// - `forbidden_vars`: Variables that may not be modified.
    /// - `bindings`: Optional function-parameter bindings.
    ///
    /// # Returns
    /// `Some(Value::Real)` containing the computed norm.
    ///
    /// # Panics
    /// This function **may panic only** if `i64_to_f64_checked` is called with
    /// an incorrectly constructed error (i.e., an internal misuse of
    /// `RuntimeError::LiteralTooLarge`).
    /// Under correct interpreter behavior, this situation does not occur.
    ///
    /// # Example
    /// ```
    /// use std::collections::HashSet;
    ///
    /// use arithma::{
    ///     ast::{Expr, LiteralValue},
    ///     interpreter::{evaluator::core::Context, value::core::Value},
    /// };
    ///
    /// let mut context = Context::new();
    ///
    /// // norm([3, 4]) = 5
    /// let array = Expr::ArrayLiteral { elements: vec![Expr::Literal { value: 3.into(),
    ///                                                                 line:  1, },
    ///                                                 Expr::Literal { value: 4.into(),
    ///                                                                 line:  1, },],
    ///                                  line:     1, };
    ///
    /// let result = context.eval_norm(&array, 1, &HashSet::new(), None).unwrap();
    ///
    /// assert_eq!(result, Some(Value::Real(5.0)));
    /// ```
    pub fn eval_norm(&mut self,
                     array: &Expr,
                     line: usize,
                     forbidden_vars: &HashSet<String>,
                     bindings: Option<&HashMap<String, Value>>)
                     -> EvalResult<Option<Value>> {
        let array_value = self.eval(array, forbidden_vars, bindings)?
                              .ok_or(RuntimeError::MissingValue { line })?;

        match array_value {
            Value::Array(ref arr) if arr.is_empty() => Ok(Some(Value::Real(0.0))),
            Value::Array(ref arr) => {
                let all_integers = arr.iter().all(Value::is_integer);

                if all_integers {
                    let mut squared_sum: i64 = 0;
                    for x in arr.iter() {
                        if let Value::Integer(i) = x {
                            let sq = i * i;
                            squared_sum = squared_sum
                                .checked_add(sq)
                                .ok_or(RuntimeError::Overflow { line })?;
                        }
                    }
                    Ok(Some(Value::Real(
                        (i64_to_f64_checked(squared_sum, RuntimeError::LiteralTooLarge { line })?)
                            .sqrt(),
                    )))
                } else {
                    let mut squared_sum = 0.0;
                    for x in arr.iter() {
                        let f = x.as_numeric_f64(line)?;
                        squared_sum += f * f;
                    }
                    Ok(Some(Value::Real(squared_sum.sqrt())))
                }
            },
            _ => Err(RuntimeError::TypeError {
                details: "Tried to evaluate the norm of a non-array value".to_string(),
                line,
            }),
        }
    }

    /// Pushes a new local scope.
    ///
    /// A fresh empty scope is added on top of the scope stack.
    /// This is used for blocks, function bodies and any construct that requires
    /// lexical scoping.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::evaluator::core::Context;
    ///
    /// let mut context = Context::new();
    /// let initial = context.scope_stack.len();
    ///
    /// context.push_scope();
    ///
    /// assert_eq!(context.scope_stack.len(), initial + 1);
    /// ```
    pub fn push_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }

    /// Removes the innermost local scope.
    ///
    /// This is called when leaving a block or function body.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::evaluator::core::Context;
    ///
    /// let mut context = Context::new();
    /// context.push_scope();
    /// let before = context.scope_stack.len();
    ///
    /// context.pop_scope();
    ///
    /// assert_eq!(context.scope_stack.len(), before - 1);
    /// ```
    pub fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    /// Retrieves a variable from the current scope stack.
    ///
    /// Lookup begins at the innermost scope and proceeds outward toward the
    /// global scope. Returns `None` if the variable is not defined in any
    /// active scope.
    ///
    /// # Parameters
    /// - `name`: Variable name.
    ///
    /// # Returns
    /// A reference to the value if found, otherwise `None`.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let mut context = Context::new();
    /// context.define_local("x", Value::Integer(5));
    ///
    /// assert_eq!(context.get_variable("x"), Some(&Value::Integer(5)));
    /// assert_eq!(context.get_variable("y"), None);
    /// ```
    #[must_use]
    pub fn get_variable(&self, name: &str) -> Option<&Value> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v);
            }
        }
        None
    }

    /// Defines a variable in the current (innermost) scope.
    ///
    /// Inserts the variable into the topmost scope.
    /// Used for declarations and for creating new bindings in blocks or
    /// function bodies.
    ///
    /// # Parameters
    /// - `name`: Variable name.
    /// - `value`: Value to store.
    ///
    /// # Panics
    /// Panics if no scope exists, which indicates an internal error.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let mut context = Context::new();
    /// context.define_local("a", Value::Integer(1));
    ///
    /// assert_eq!(context.get_variable("a"), Some(&Value::Integer(1)));
    /// ```
    pub fn define_local(&mut self, name: &str, value: Value) {
        self.scope_stack
            .last_mut()
            .expect("at least global")
            .insert(name.to_string(), value);
    }

    /// Assigns a value to an existing variable if present, otherwise defines
    /// it.
    ///
    /// The assignment searches from the innermost scope outward.
    /// If the variable does not exist in any scope, it is added to the current
    /// scope. If no scopes exist, a new one is created containing the
    /// variable.
    ///
    /// # Parameters
    /// - `name`: Variable name.
    /// - `value`: Value to assign.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let mut context = Context::new();
    ///
    /// context.set_variable("x".into(), Value::Integer(10));
    /// assert_eq!(context.get_variable("x"), Some(&Value::Integer(10)));
    ///
    /// context.set_variable("x".into(), Value::Integer(20));
    /// assert_eq!(context.get_variable("x"), Some(&Value::Integer(20)));
    /// ```
    pub fn set_variable(&mut self, name: String, value: Value) {
        for scope in self.scope_stack.iter_mut().rev() {
            if let std::collections::hash_map::Entry::Occupied(mut e) = scope.entry(name.clone()) {
                e.insert(value);
                return;
            }
        }
        if let Some(current) = self.scope_stack.last_mut() {
            current.insert(name, value);
        } else {
            self.scope_stack.push(HashMap::from([(name, value)]));
        }
    }

    /// Assigns a value to the nearest scope containing the variable.
    ///
    /// Search proceeds from the innermost scope outward.
    /// If the variable is not found, it is inserted into the current scope.
    /// This differs from `set_variable` because it does not treat creation as
    /// an equal alternative.
    ///
    /// # Parameters
    /// - `name`: Variable to update.
    /// - `value`: New value.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let mut context = Context::new();
    /// context.define_local("y", Value::Integer(1));
    ///
    /// context.assign_nearest("y", Value::Integer(5));
    ///
    /// assert_eq!(context.get_variable("y"), Some(&Value::Integer(5)));
    /// ```
    pub fn assign_nearest(&mut self, name: &str, value: Value) {
        for scope in self.scope_stack.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        if let Some(scope) = self.scope_stack.last_mut() {
            scope.insert(name.to_string(), value);
        } else {
            self.scope_stack
                .push(HashMap::from([(name.to_string(), value)]));
        }
    }

    /// Pushes a new scope and returns a guard that will pop it automatically.
    ///
    /// This is an RAII helper used to ensure scopes are properly unwound even
    /// when errors occur. The returned `ScopeGuard` removes the scope when
    /// dropped.
    ///
    /// # Returns
    /// A `ScopeGuard` managing the new scope.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::evaluator::core::Context;
    ///
    /// let mut context = Context::new();
    /// let before = context.scope_stack.len();
    ///
    /// {
    ///     let _guard = context.scoped();
    ///     assert_eq!(context.scope_stack.len(), before + 1);
    /// }
    ///
    /// assert_eq!(context.scope_stack.len(), before);
    /// ```
    pub fn scoped(&mut self) -> ScopeGuard {
        self.push_scope();
        ScopeGuard { context_pointer: self, }
    }
}

/// Checks if the argument list matches the expected count.
/// Returns an error if the argument count does not match.
///
/// ## Example
/// ```
/// use arithma::interpreter::{evaluator::utils::check_arity, value::core::Value};
///
/// let arg_vals = vec![Value::Integer(2), Value::Integer(1)];
/// let line = 15;
///
/// assert!(check_arity(&arg_vals, 2, line).is_ok()); // Requires exactly 2 arguments.
/// ```
pub const fn check_arity<T>(args: &[T], expected: usize, line: usize) -> EvalResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(RuntimeError::ArgumentCountMismatch { line })
    }
}

/// Computes the multi-factorial of a number.
///
/// Multi-factorial generalizes the standard factorial operation:\
/// Instead of decrementing by 1, this function multiplies `k` by values
/// decreasing by `n` each time, until reaching 1 or below.
///
/// Returns `k` directly if `n == 0` (by convention; mathematically undefined).
/// ## Example
/// ```
/// use arithma::interpreter::evaluator::utils::multi_factorial;
///
/// // Single factorial: 5!
/// let fact = multi_factorial(5, 1, 42).unwrap();
/// assert_eq!(fact, 120);
///
/// // Double factorial: 7!!
/// let double_fact = multi_factorial(7, 2, 42).unwrap();
/// assert_eq!(double_fact, 105); // 7 * 5 * 3 * 1
///
/// // Triple factorial: 7!!!
/// let triple_fact = multi_factorial(7, 3, 42).unwrap();
/// assert_eq!(triple_fact, 28); // 7 * 4 * 1
///
/// // By convention: n == 0 returns k directly
/// let degenerate = multi_factorial(99, 0, 42).unwrap();
/// assert_eq!(degenerate, 99);
/// ```
///
/// ## Parameters
/// - `k`: The number to compute the multi-factorial of. (u64)
/// - `n`: The decrement ("step size"). Use 1 for standard factorial, 2 for
///   double factorial, etc. (u8)
/// - `line`: Line number in the source, for error reporting. (usize)
///
/// ## Returns
/// - `Ok(u64)`: The computed multi-factorial value.
/// - `Err(RuntimeError::Overflow { line })`: If an overflow occurs during
///   computation.
pub fn multi_factorial(k: u64, n: u8, line: usize) -> EvalResult<u64> {
    if n == 0 {
        return Ok(k);
    }

    if k == 0 || k == 1 {
        return Ok(1);
    }

    let mut result = 1u64;

    let mut current = k;
    while current > 1 {
        result = result.checked_mul(current)
                       .ok_or(RuntimeError::Overflow { line })?;

        if current <= u64::from(n) {
            break;
        }

        current -= u64::from(n);
    }
    Ok(result)
}

/// Computes the gamma function Γ(z) using the Lanczos approximation.
///
/// This implementation uses the standard 9-term Lanczos coefficients
/// (`g = 7`) and supports all finite real inputs except negative integers and
/// zero, where the gamma function has poles.  
///
/// For `z < 0.5`, the reflection formula is applied:
///
/// `Γ(z) = π / (sin(πz) * Γ(1 − z))`
///
/// For `z ≥ 0.5`, the Lanczos approximation is evaluated directly using numeric
/// checks to avoid invalid conversions.
///
/// # Parameters
/// - `z`: Input value.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Ok(Γ(z))`, or a `RuntimeError` if `z` lies at a pole or if an internal
/// conversion check fails.
///
/// # Panics
/// This function **does not normally panic**.
/// A panic is only possible if numeric helper routines (such as
/// `usize_to_f64_checked`) are misused internally, which cannot happen during
/// normal interpreter evaluation.
///
/// # Example
/// ```
/// use arithma::interpreter::evaluator::utils::euler_gamma;
///
/// // Γ(5) = 4! = 24
/// let g = euler_gamma(5.0, 1).unwrap();
/// assert!((g - 24.0).abs() < 1e-12);
/// ```
pub fn euler_gamma(z: f64, line: usize) -> EvalResult<f64> {
    // Lanczos coefficients, g = 7, n = 9.
    // These are standard values from Numerical recipes.
    const COEFFS: [f64; 9] = [0.999_999_999_999_809_9,
                              676.520_368_121_885_1,
                              -1_259.139_216_722_402_8,
                              771.323_428_777_653_1,
                              -176.615_029_162_140_6,
                              12.507_343_278_686_905,
                              -0.138_571_095_265_720_12,
                              9.984_369_578_019_572e-6,
                              1.505_632_735_149_311_6e-7];
    const G: f64 = 7.0;

    if z < 0.5 {
        Ok(std::f64::consts::PI / ((std::f64::consts::PI * z).sin() * euler_gamma(1.0 - z, line)?))
    } else {
        let z_minus_1 = z - 1.0;
        let mut x = COEFFS[0];

        for (i, &c) in COEFFS.iter().enumerate().skip(1) {
            x += c / (z_minus_1 + usize_to_f64_checked(i, line)?);
        }

        let t = z_minus_1 + G + 0.5;

        Ok((std::f64::consts::TAU).sqrt() * t.powf(z_minus_1 + 0.5) * (-t).exp() * x)
    }
}

/// Compares two numeric values for approximate equality.
///
/// Both operands are promoted to a common numeric type before comparison.
/// The comparison uses the standard tolerance rule:
///
/// `|a − b| ≤ max(abs_tol, rel_tol * max(|a|, |b|))`
///
/// Integers use exact equality.
/// Reals and complex values use their absolute magnitude when computing the
/// tolerance condition.
///
/// # Parameters
/// - `left`: First value.
/// - `right`: Second value.
/// - `abs_tol`: Absolute tolerance.
/// - `rel_tol`: Relative tolerance.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Ok(true)` if the values are approximately equal within the given
/// tolerances.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::utils::is_close, value::core::Value};
///
/// let a = Value::Real(1.0000000001);
/// let b = Value::Real(1.0);
///
/// let result = is_close(&a, &b, 1e-11, 1e-9, 1).unwrap();
///
/// // Use approximate check, not exact equality
/// assert!(result);
/// ```
pub fn is_close(left: &Value,
                right: &Value,
                abs_tol: f64,
                rel_tol: f64,
                line: usize)
                -> EvalResult<bool> {
    let (left, right) = promote_for_compare(left, right, line)?;

    match (left, right) {
        (Value::Integer(a), Value::Integer(b)) => Ok(a == b),

        (Value::Real(a), Value::Real(b)) => {
            let difference = (a - b).abs();
            let max_norm = a.abs().max(b.abs());
            Ok(difference <= abs_tol.max(rel_tol * max_norm))
        },

        (Value::Complex(a), Value::Complex(b)) => {
            let diff = ComplexNumber { real:      a.real - b.real,
                                       imaginary: a.imaginary - b.imaginary, }.abs();

            let max_norm = a.abs().max(b.abs());

            Ok(diff <= abs_tol.max(rel_tol * max_norm))
        },

        _ => unreachable!("promote_for_compare guarantees matched types"),
    }
}

/// Checks whether a name refers to a reserved identifier.
///
/// A reserved identifier is either:
/// - a builtin function name, or
/// - an internally reserved keyword used by the evaluator.
///
/// This prevents redefinition of builtin functionality.
///
/// # Parameters
/// - `name`: Identifier to check.
///
/// # Returns
/// `true` if the name is reserved, otherwise `false`.
///
/// # Example
/// ```
/// use arithma::interpreter::evaluator::utils::is_reserved_identifier;
///
/// assert!(is_reserved_identifier("sin"));
/// assert!(!is_reserved_identifier("my_function"));
/// ```
#[must_use]
pub fn is_reserved_identifier(name: &str) -> bool {
    use crate::interpreter::evaluator::function::core::BUILTIN_FUNCTIONS;

    BUILTIN_FUNCTIONS.contains(&name) || EXTRA_RESERVED.contains(&name)
}

/// Promotes two numeric values to a common type for comparison.
///
/// The promotion rules are:
/// - `Integer` + `Integer` -> `Real` + `Real` (checked integer->float
///   conversion)
/// - `Integer` + `Real`    -> `Real` + `Real`
/// - `Real`    + `Integer` -> `Real` + `Real`
/// - `Real`    + `Real`    -> `Real` + `Real`
/// - otherwise both values are promoted to complex.
///
/// This ensures that comparison operations (`is_close`, ordering, etc.)
/// always operate on compatible numeric types.
///
/// # Parameters
/// - `a`: First value.
/// - `b`: Second value.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// A tuple `(Value, Value)` of promoted values.
///
/// # Panics
/// Never panics; checked conversions return `RuntimeError` instead.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::utils::promote_for_compare, value::core::Value};
///
/// let (a, b) = promote_for_compare(&Value::Integer(3), &Value::Real(4.0), 1).unwrap();
///
/// assert!(matches!(a, Value::Real(_)));
/// assert!(matches!(b, Value::Real(_)));
/// ```
pub fn promote_for_compare(a: &Value, b: &Value, line: usize) -> EvalResult<(Value, Value)> {
    use Value::{Integer, Real};

    match (a, b) {
        (Integer(x), Integer(y)) => {
            Ok((Real(i64_to_f64_checked(*x, RuntimeError::LiteralTooLarge { line })?),
                Real(i64_to_f64_checked(*y, RuntimeError::LiteralTooLarge { line })?)))
        },

        (Integer(x), Real(y)) => {
            Ok((Real(i64_to_f64_checked(*x, RuntimeError::LiteralTooLarge { line })?), Real(*y)))
        },
        (Real(x), Integer(y)) => {
            Ok((Real(*x), Real(i64_to_f64_checked(*y, RuntimeError::LiteralTooLarge { line })?)))
        },
        (Real(x), Real(y)) => Ok((Real(*x), Real(*y))),

        _ => {
            let (a_complex, b_complex) = a.clone().promote_to_complex(b, line)?;
            Ok((a_complex, b_complex))
        },
    }
}

/// Checks strict equality between two values, performing minimal promotion.
///
/// Rules:
/// - If either operand is complex, both are promoted to complex and compared.
/// - Else if either operand is real, both are promoted to real and compared.
/// - Otherwise, values are compared directly (integers, booleans, arrays,
///   sets).
///
/// This is used for exact comparisons (`==`, `!=`) as opposed to approximate
/// numeric equality.
///
/// # Parameters
/// - `left`: First value.
/// - `right`: Second value.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `true` if values are equal after promotion.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::utils::strict_eq, value::core::Value};
///
/// let a = Value::Real(2.0);
/// let b = Value::Integer(2);
///
/// // Strict equality promotes integer to real.
/// assert!(strict_eq(&a, &b, 1).unwrap());
/// ```
pub fn strict_eq(left: &Value, right: &Value, line: usize) -> EvalResult<bool> {
    match (left, right) {
        (Value::Complex(_), _) | (_, Value::Complex(_)) => {
            let (l, r) = left.clone().promote_to_complex(right, line)?;
            Ok(l == r)
        },

        (Value::Real(_), _) | (_, Value::Real(_)) => {
            let (l, r) = left.clone().promote_to_real(right, line)?;
            Ok(l == r)
        },

        _ => Ok(left == right),
    }
}
