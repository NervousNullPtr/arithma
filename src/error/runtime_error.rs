#[derive(Debug)]
/// Represents all errors that can occur during evaluation and runtime.
pub enum RuntimeError {
    /// Tried to use an undefined variable.
    UnknownVariable {
        /// The name of the variable.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// Called an unknown function.
    UnknownFunction {
        /// The name of the function.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// Tried to declare a variable that would shadow an existing one.
    VariableShadowing {
        /// The name of the variable.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// Attempted to define a function that already exists.
    FunctionAlreadyDefined {
        /// The name of the function.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// Attempted to redefine a built-in function.
    BuiltinFunctionRedefinition {
        /// The name of the function.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// Loop bounds are invalid or nonsensical.
    InvalidLoopBounds {
        /// Details describing why the bounds are invalid.
        details: String,
        /// The source line where the error occurred.
        line:    usize,
    },
    /// Tried to assign to the current loop variable (not allowed).
    AssignmentToLoopVariable {
        /// The name of the loop variable.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// A value had an unexpected or incompatible type.
    TypeError {
        /// Details about the type mismatch.
        details: String,
        /// The source line where the error occurred.
        line:    usize,
    },
    /// A boolean value was expected, but not found.
    ExpectedBoolean {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A numeric value was expected, but not found.
    ExpectedNumber {
        /// The source line where the error occurred.
        line: usize,
    },
    /// An array value was expected, but not found.
    ExpectedArray {
        /// The source line where the error occurred.
        line: usize,
    },
    /// An argument was invalid or out of range.
    InvalidArgument {
        /// Details about why the argument is invalid.
        details: String,
        /// The source line where the error occurred.
        line:    usize,
    },
    /// The wrong number of arguments was supplied to a function.
    ArgumentCountMismatch {
        /// The source line where the error occurred.
        line: usize,
    },
    /// An expected value was missing (e.g., in an assignment or function).
    MissingValue {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Encountered an unknown or unsupported expression type.
    UnknownExpression {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Arithmetic operation overflowed.
    Overflow {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Tried to access an array/set element outside the allowed bounds.
    IndexOutOfBounds {
        /// The largest valid index.
        max:   usize,
        /// The index that was actually requested.
        found: usize,
        /// The source line where the error occurred.
        line:  usize,
    },
    /// An assertion failed during execution.
    AssertionFailed {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Attempted division by zero.
    DivisionByZero {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A literal value was too large to be represented safely.
    LiteralTooLarge {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Tried to use a real number where an integer was required.
    RealIsFractional {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A literal value was too small to be represented safely.
    LiteralTooSmall {
        /// The source line where the error occurred.
        line: usize,
    },
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownVariable { name, line } => {
                write!(f, "Error on line {line}: Unknown variable '{name}'.")
            },
            Self::UnknownFunction { name, line } => {
                write!(f, "Error on line {line}: Unknown function '{name}'.")
            },
            Self::VariableShadowing { name, line } => write!(f,
                                                             "Error on line {line}: Variable shadowing is not allowed: '{name}'."),

            Self::FunctionAlreadyDefined { name, line } => write!(f,
                                                                  "Error on line {line}: Function '{name}' is already defined."),
            Self::BuiltinFunctionRedefinition { name, line } => write!(f,
                                                                       "Error on line {line}: Cannot redefine built-in function '{name}'."),

            Self::InvalidLoopBounds { details, line } => {
                write!(f, "Error on line {line}: Invalid loop bounds: {details}.")
            },
            Self::AssignmentToLoopVariable { name, line } => write!(f,
                                                                    "Error on line {line}: Assignment to loop variable '{name}' is not allowed."),

            Self::TypeError { details, line } => {
                write!(f, "Error on line {line}: Type error: {details}.")
            },
            Self::ExpectedBoolean { line } => write!(f, "Error on line {line}: Expected boolean."),
            Self::ExpectedNumber { line } => write!(f, "Error on line {line}: Expected number."),
            Self::ExpectedArray { line } => write!(f, "Error on line {line}: Expected array."),
            Self::InvalidArgument { details, line } => {
                write!(f, "Error on line {line}: Invalid argument: {details}.")
            },
            Self::ArgumentCountMismatch { line } => {
                write!(f, "Error on line {line}: Argument count mismatch.")
            },

            Self::MissingValue { line } => write!(f, "Error on line {line}: Value missing."),
            Self::UnknownExpression { line } => {
                write!(f, "Error on line {line}: Expression is unknown.")
            },

            Self::Overflow { line } => write!(f,
                                              "Error on line {line}: Integer overflow while trying to compute result."),
            Self::IndexOutOfBounds { max, found, line } => write!(f,
                                                                  "Error on line {line}: Index out of bounds. Maximum is {max}, but found {found} instead."),
            Self::AssertionFailed { line } => write!(f, "Error on line {line}: Assertion failed."),
            Self::DivisionByZero { line } => write!(f, "Error on line {line}: Division by zero."),
            Self::LiteralTooLarge { line } => {
                write!(f, "Error on line {line}: Literal is too large.")
            },
            Self::RealIsFractional { line } => write!(f,
                                                      "Error on line {line}: Value is fractional and cannot be safely converted to a number."),
            Self::LiteralTooSmall { line } => {
                write!(f, "Error on line {line}: Literal is too small.")
            },
        }
    }
}

impl std::error::Error for RuntimeError {}
