#[derive(Debug)]
/// Represents all errors that can occur during lexing or parsing.
pub enum ParseError {
    /// Found an unexpected token while parsing.
    UnexpectedToken {
        /// The token encountered.
        token: String,
        /// The source line where the error occurred.
        line:  usize,
    },
    /// Reached the end of input unexpectedly.
    UnexpectedEndOfInput {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A closing parenthesis `)` was expected but not found.
    ExpectedClosingParen {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A `|` token was expected but not found.
    ExpectedPipe {
        /// The source line where the error occurred.
        line: usize,
    },
    /// A `||` token was expected but not found.
    ExpectedDoublePipe {
        /// The source line where the error occurred.
        line: usize,
    },
    /// The function definition syntax was invalid.
    InvalidFunctionDefinition {
        /// The source line where the error occurred.
        line: usize,
    },
    /// Found extra tokens after parsing should have completed.
    UnexpectedTrailingTokens {
        /// The extra/unexpected token.
        token: String,
        /// The source line where the error occurred.
        line:  usize,
    },
    /// Too many factorial operators were applied.
    TooManyFactorials {
        /// The number of consecutive factorials.
        count: u8,
        /// The source line where the error occurred.
        line:  usize,
    },
    /// Some other kind of parse error, with a custom message.
    Other {
        /// Details about the parse error.
        message: String,
        /// The source line where the error occurred.
        line:    usize,
    },
    /// Tried to use a reserved identifier name.
    IdentifierReserved {
        /// The reserved identifier name.
        name: String,
        /// The source line where the error occurred.
        line: usize,
    },
    /// A literal value was too large to be represented safely.
    LiteralTooLarge {
        /// The source line where the error occurred.
        line: usize,
    },
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedToken { token, line } => {
                write!(f, "Error on line {line}: Unexpected token: {token}.")
            },

            Self::UnexpectedEndOfInput { line } => {
                write!(f, "Error on line {line}: Unexpected end of input.")
            },

            Self::ExpectedClosingParen { line } => write!(f,
                                                          "Error on line {line}: Expected closing parenthesis ')' but none found."),

            Self::ExpectedPipe { line } => {
                write!(f, "Error on line {line}: Expected pipe '|' but none found.")
            },

            Self::ExpectedDoublePipe { line } => write!(f,
                                                        "Error on line {line}: Expected double pipe '||' but none found."),

            Self::InvalidFunctionDefinition { line } => write!(f,
                                                               "Error on line {line}: Invalid function definition syntax. Example: f(x) = x * x"),

            Self::UnexpectedTrailingTokens { token, line } => write!(f,
                                                                     "Error on line {line}: Extra tokens after expression. Check your input: {token}"),

            Self::TooManyFactorials { count, line } => {
                write!(f, "Error on line {line}: {count} factorials is too many.")
            },

            Self::Other { message, line } => write!(f, "Error on line {line}: {message}"),

            Self::IdentifierReserved { name, line } => {
                write!(f, "Error on line {line}: Identifier {name} is reserved.")
            },
            Self::LiteralTooLarge { line } => {
                write!(f, "Error on line {line}: Literal is too large.")
            },
        }
    }
}

impl std::error::Error for ParseError {}
