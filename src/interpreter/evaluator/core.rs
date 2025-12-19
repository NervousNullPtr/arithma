use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Expr, FunctionDef, Statement},
    error::RuntimeError,
    interpreter::{evaluator::function::core::validate_function_name, value::core::Value},
};

/// Result type used by the evaluator.
///
/// All evaluation functions return either a value of type `T` or a
/// `RuntimeError` describing the failure.
pub type EvalResult<T> = Result<T, RuntimeError>;

/// Default relative tolerance used for approximate comparisons.
pub const REL_TOLERANCE: f64 = 1e-10;
/// Default absolute tolerance used for approximate comparisons.
pub const ABS_TOLERANCE: f64 = 0.0;

/// Stores the runtime evaluation context.
///
/// This struct holds the interpreter state, including all user defined
/// functions and variable assignments used during evaluation.
///
/// ## Usage
///
/// `Context` is created once and reused for evaluating expressions and
/// statements. All evaluation methods (like `eval()` and `eval_with_binding()`)
/// access this state to resolve variables and functions.
pub struct Context {
    pub scope_stack:   Vec<HashMap<String, Value>>,
    /// A mapping from function names to their [`FunctionDef`] definitions.
    /// Populated when declaring functions like `square(x) = x * x`.
    pub functions:     HashMap<String, FunctionDef>,
    /// Relative tolerance for approximately equal.
    pub rel_tolerance: f64,
    /// Absolute tolerance for approximately equal.
    pub abs_tolerance: f64,
}

#[allow(clippy::new_without_default)]
impl Context {
    /// Creates a new evaluation context with empty scope and no user-defined
    /// functions. Tolerances are initialized to the global defaults.
    #[must_use]
    pub fn new() -> Self {
        Self { scope_stack:   vec![HashMap::new()],
               functions:     HashMap::new(),
               rel_tolerance: REL_TOLERANCE,
               abs_tolerance: ABS_TOLERANCE, }
    }
    /// Evaluates an expression and returns the resulting value.
    ///
    /// This is the main entry point for expression evaluation.
    /// The evaluator dispatches based on expression variant:
    /// literals, variables, unary and binary operations, function calls,
    /// absolute values, conditional expressions, loops, blocks, array indexing,
    /// norms and set literals.
    ///
    /// # Parameters
    /// - `expr`: Expression to evaluate.
    /// - `forbidden_vars`: Variables that cannot be assigned inside loops.
    /// - `bindings`: Optional parameter bindings for function bodies.
    ///
    /// # Returns
    /// `Some(Value)` for expressions that produce a value, or `None` for
    /// constructs that do not yield one.
    pub fn eval(&mut self,
                expr: &Expr,
                forbidden_vars: &HashSet<String>,
                bindings: Option<&HashMap<String, Value>>)
                -> EvalResult<Option<Value>> {
        match expr {
            Expr::Literal { value, .. } => Self::eval_literal(value),
            Expr::Variable { name, line } => self.eval_variable(name, *line, bindings),
            Expr::UnaryOp { op, expr, line } => {
                self.eval_unary_op(*op, expr, *line, forbidden_vars, bindings)
            },
            Expr::BinaryOp { left,
                             op,
                             right,
                             line,
                             rel_tolerance,
                             abs_tolerance, } => self.eval_binary_op(left,
                                                                     *op,
                                                                     right,
                                                                     *line,
                                                                     forbidden_vars,
                                                                     *rel_tolerance,
                                                                     *abs_tolerance,
                                                                     bindings),
            Expr::FunctionCall { name,
                                 arguments,
                                 line, } => {
                let v = self.eval_function_call(name, arguments, *line, forbidden_vars, bindings)?;
                Ok(Some(v))
            },
            Expr::Abs { expr, line } => self.eval_abs(expr, *line, forbidden_vars, bindings),
            Expr::IfExpr { condition,
                           then_branch,
                           else_branch,
                           line, } => self.eval_if_expr(condition,
                                                        then_branch,
                                                        else_branch.as_deref(),
                                                        *line,
                                                        forbidden_vars,
                                                        bindings),
            Expr::ForExpr { context, line } => {
                self.eval_for(context, bindings, forbidden_vars, *line)
            },
            Expr::Block { statements, .. } => self.eval_block(statements, forbidden_vars, bindings),
            Expr::ArrayLiteral { elements, line } => {
                self.eval_array_literal(elements, *line, forbidden_vars, bindings)
            },
            Expr::ArrayIndex { array, index, line } => {
                self.eval_array_index(array, index, *line, forbidden_vars, bindings)
            },
            Expr::Norm { expr, line } => self.eval_norm(expr, *line, forbidden_vars, bindings),
            Expr::SetLiteral { elements, line } => {
                self.eval_set_literal(elements, *line, forbidden_vars, bindings)
            },
        }
    }

    /// Evaluates a single statement.
    ///
    /// Handles variable declarations, assignments, function definitions,
    /// compound assignments, tolerance configuration and plain expression
    /// statements. Statements may modify the context or produce a value.
    ///
    /// # Parameters
    /// - `statement`: Statement to evaluate.
    /// - `bindings`: Optional function parameter bindings.
    /// - `forbidden_vars`: Variables that cannot be modified inside loops.
    ///
    /// # Returns
    /// `Some(Value)` for statements that yield a result, or `None` when no
    /// value is produced.
    pub fn eval_statement(&mut self,
                          statement: &Statement,
                          bindings: Option<&HashMap<String, Value>>,
                          forbidden_vars: &HashSet<String>)
                          -> EvalResult<Option<Value>> {
        match statement {
            Statement::Function(def) => {
                validate_function_name(self, &def.name, def.line)?;
                self.functions.insert(def.name.clone(), def.clone());
                Ok(None)
            },
            Statement::VariableDeclaration { name, value, line } => {
                if forbidden_vars.contains(name) {
                    return Err(RuntimeError::AssignmentToLoopVariable { name: name.clone(),
                                                                        line: *line, });
                }

                let value = self.eval(value, forbidden_vars, bindings)?
                                .ok_or(RuntimeError::MissingValue { line: *line })?;

                self.define_local(name, value.clone());
                Ok(Some(value))
            },
            Statement::Assignment { name, value, line } => {
                if forbidden_vars.contains(name) {
                    return Err(RuntimeError::AssignmentToLoopVariable { name: name.clone(),
                                                                        line: *line, });
                }

                if self.get_variable(name).is_none() {
                    return Err(RuntimeError::UnknownVariable { name: name.clone(),
                                                               line: *line, });
                }

                let value = self.eval(value, forbidden_vars, bindings)?
                                .ok_or(RuntimeError::MissingValue { line: *line })?;

                self.assign_nearest(name, value.clone());
                Ok(Some(value))
            },
            Statement::Expression { expr, .. } => self.eval(expr, forbidden_vars, bindings),
            Statement::CompoundAssignment { name,
                                            op,
                                            value,
                                            line, } => {
                if forbidden_vars.contains(name) {
                    return Err(RuntimeError::AssignmentToLoopVariable { name: name.clone(),
                                                                        line: *line, });
                }

                let old_value = self.get_variable(name)
                                    .ok_or_else(|| RuntimeError::UnknownVariable { name:
                                                                                       name.clone(),
                                                                                   line: *line, })?
                                    .clone();

                let rhs_value = self.eval(value, forbidden_vars, bindings)?
                                    .ok_or(RuntimeError::MissingValue { line: *line })?;
                let result = self.eval_binary(*op, &old_value, &rhs_value, *line, None, None)?;

                self.assign_nearest(name, result.clone());
                Ok(Some(result))
            },
            Statement::SetRelTolerance(tol) => {
                self.rel_tolerance = *tol;
                Ok(None)
            },
            Statement::SetAbsTolerance(tol) => {
                self.abs_tolerance = *tol;
                Ok(None)
            },
        }
    }
}
