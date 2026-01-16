use std::collections::{HashMap, HashSet};

use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{
            core::{Context, EvalResult},
            function::{builtin, clamp, conj, log, min_max, print, sqrt, transpose, trunc, choose},
        },
        value::core::Value,
    },
};

/// Type alias for builtin function handlers.
///
/// A builtin receives a slice of evaluated argument values and the line number.
/// It returns an optional value wrapped in `EvalResult`.
type BuiltinFn = fn(&[Value], usize) -> EvalResult<Value>;

/// Specifies the allowed number of arguments for a builtin.
///
/// - `Exact(n)` means the builtin must receive exactly `n` arguments.
/// - `OneOf(slice)` means the builtin accepts any arity listed in `slice`.
#[derive(Clone, Copy)]
enum Arity {
    Exact(usize),
    OneOf(&'static [usize]),
}

/// Defines builtin functions by generating a lookup table and a name list.
///
/// Each entry provides:
/// - a string name,
/// - an arity specification,
/// - a function pointer implementing the builtin.
///
/// The macro produces:
/// - `BuiltinDef` (internal metadata),
/// - `BUILTIN_TABLE` (static table for lookup),
/// - `BUILTIN_FUNCTIONS` (public list of builtin names).
macro_rules! builtin_functions {
    (
        $(
            $name:literal => {
                arity: $arity:expr,
                func: $func:expr $(,)?
            }
        ),* $(,)?
    ) => {
        struct BuiltinDef {
            name:  &'static str,
            arity: Arity,
            func:  BuiltinFn,
        }
        static BUILTIN_TABLE: &[BuiltinDef] = &[
            $(
                BuiltinDef { name: $name, arity: $arity, func: $func },
            )*
        ];
        pub const BUILTIN_FUNCTIONS: &[&str] = &[
            $($name,)*
        ];
    };
}

builtin_functions! {
    "ln"      => { arity: Arity::Exact(1), func: builtin::ln },
    "sin"     => { arity: Arity::Exact(1), func: builtin::sin },
    "cos"     => { arity: Arity::Exact(1), func: builtin::cos },
    "tan"     => { arity: Arity::Exact(1), func: builtin::tan },
    "sinh"    => { arity: Arity::Exact(1), func: builtin::sinh },
    "cosh"    => { arity: Arity::Exact(1), func: builtin::cosh },
    "tanh"    => { arity: Arity::Exact(1), func: builtin::tanh },
    "exp"     => { arity: Arity::Exact(1), func: builtin::exp },
    "radians" => { arity: Arity::Exact(1), func: builtin::radians },
    "degrees" => { arity: Arity::Exact(1), func: builtin::degrees },
    "sign"    => { arity: Arity::Exact(1), func: builtin::sign },
    "assert"  => { arity: Arity::Exact(1), func: builtin::assert_fn },
    "sqrt"    => { arity: Arity::OneOf(&[1,2]), func: sqrt::sqrt },
    "conj"    => { arity: Arity::Exact(1), func: conj::conj },
    "clamp"   => { arity: Arity::Exact(3), func: clamp::clamp },
    "min"     => { arity: Arity::Exact(2), func: |args, line| min_max::min_max("min", args, line) },
    "max"     => { arity: Arity::Exact(2), func: |args, line| min_max::min_max("max", args, line) },
    "trunc"   => { arity: Arity::Exact(1), func: trunc::trunc },
    "log"     => { arity: Arity::Exact(2), func: log::log },
    "floor"   => { arity: Arity::Exact(1), func: |args, line| builtin::unary_round("floor", args, line) },
    "ceil"    => { arity: Arity::Exact(1), func: |args, line| builtin::unary_round("ceil", args, line) },
    "round"   => { arity: Arity::Exact(1), func: |args, line| builtin::unary_round("round", args, line) },
    "print"   => { arity: Arity::Exact(1), func: print::print },
    "trans"   => { arity: Arity::Exact(1), func: transpose::transpose },
    "choose"  => { arity: Arity::Exact(2), func: choose::choose },
}

impl Arity {
    /// Tests whether the given argument count satisfies this arity constraint.
    ///
    /// Returns `true` if the count is permitted, `false` otherwise.
    fn check(&self, n: usize) -> bool {
        match self {
            Self::Exact(m) => n == *m,
            Self::OneOf(arr) => arr.contains(&n),
        }
    }
}

impl Context {
    /// Evaluates a function call.
    ///
    /// The evaluator first checks whether the name matches a builtin.
    /// If so, it verifies arity and executes the builtin.
    /// Otherwise it delegates to user-defined function handling.
    ///
    /// # Parameters
    /// - `name`: Function name.
    /// - `arg_vals`: Evaluated argument values.
    /// - `forbidden_vars`: Variables not permitted in the call context.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// The function result or an error if lookup or arity fails.
    pub(crate) fn eval_function(&mut self,
                                name: &str,
                                arg_vals: Vec<Value>,
                                forbidden_vars: &HashSet<String>,
                                line: usize)
                                -> EvalResult<Value> {
        if let Some(builtin) = BUILTIN_TABLE.iter().find(|b| b.name == name) {
            if !builtin.arity.check(arg_vals.len()) {
                return Err(RuntimeError::ArgumentCountMismatch { line });
            }
            return (builtin.func)(&arg_vals, line);
        }

        self.call_user_defined_function(name, arg_vals, forbidden_vars, line)
    }

    /// Executes a user-defined function.
    ///
    /// The function is retrieved from the context by name.
    /// Its parameter count must match the number of supplied arguments.
    /// Parameter bindings are created and the function body is evaluated with
    /// them.
    ///
    /// # Errors
    /// - Unknown function name.
    /// - Wrong number of arguments.
    ///
    /// # Returns
    /// Optional result produced by the function body.
    fn call_user_defined_function(&mut self,
                                  name: &str,
                                  arg_vals: Vec<Value>,
                                  forbidden_vars: &HashSet<String>,
                                  line: usize)
                                  -> EvalResult<Value> {
        let func = self.functions.get(name).cloned().ok_or_else(|| {
                                                         RuntimeError::UnknownFunction {
                    name: name.to_string(),
                    line,
                }
                                                     })?;

        if arg_vals.len() != func.params.len() {
            return Err(RuntimeError::ArgumentCountMismatch { line });
        }

        let bindings = func.params
                           .iter()
                           .cloned()
                           .zip(arg_vals)
                           .collect::<HashMap<_, _>>();

        let result = self.eval(&func.body, forbidden_vars, Some(&bindings))?;

        result.map_or_else(|| Err(RuntimeError::MissingValue { line }), Ok)
    }
}

/// Ensures that a user-defined function name is valid.
///
/// A function name is rejected if:
/// - a function with the same name already exists in the context, or
/// - the name is a reserved builtin identifier.
///
/// # Parameters
/// - `context`: Current evaluation context.
/// - `name`: Name to validate.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Ok(())` if the name is allowed, otherwise an error.
pub fn validate_function_name(context: &Context, name: &str, line: usize) -> EvalResult<()> {
    use crate::interpreter::evaluator::utils::is_reserved_identifier;

    if context.functions.contains_key(name) {
        return Err(RuntimeError::FunctionAlreadyDefined { name: name.to_string(),
                                                          line });
    }
    if is_reserved_identifier(name) {
        return Err(RuntimeError::BuiltinFunctionRedefinition { name: name.to_string(),
                                                               line });
    }
    Ok(())
}
