use crate::interpreter::value::complex::ComplexNumber;

/// Represents a literal value in the language.
///
/// `LiteralValue` covers all raw, constant values that can appear directly in
/// source code, such as numbers, booleans, arrays, and sets.
/// It is used in the AST to represent literal expressions and as a convenient
/// container for constants during evaluation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LiteralValue {
    /// A 64-bit signed integer literal.
    Integer(i64),
    /// A 64-bit floating-point literal.
    Real(f64),
    /// A boolean literal value: `true` or `false`.
    Bool(bool),
    /// A complex number literal, with real and imaginary parts.
    Complex(ComplexNumber),
}

impl<T: Into<Self> + Clone> From<&T> for LiteralValue {
    fn from(v: &T) -> Self {
        v.clone().into()
    }
}

impl From<i64> for LiteralValue {
    fn from(value: i64) -> Self {
        Self::Integer(value)
    }
}

impl From<f64> for LiteralValue {
    fn from(value: f64) -> Self {
        Self::Real(value)
    }
}

impl From<bool> for LiteralValue {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<ComplexNumber> for LiteralValue {
    fn from(value: ComplexNumber) -> Self {
        Self::Complex(value)
    }
}

impl From<(f64, f64)> for LiteralValue {
    fn from(value: (f64, f64)) -> Self {
        Self::Complex(ComplexNumber { real:      value.0,
                                      imaginary: value.1, })
    }
}

/// An abstract syntax tree (AST) node representing an expression in the
/// language.
///
/// `Expr` covers all types of expressions, from literals and variables to
/// function calls, arithmetic, conditionals, blocks, arrays, and sets. Each
/// variant models a distinct syntactic construct and may contain fields for
/// operands, names, source location, and (for binary operations) optional
/// tolerances for approximate comparison.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal value (number, string, boolean, etc.).
    Literal {
        /// The constant value.
        value: LiteralValue,
        /// Line number in the source code.
        line:  usize,
    },
    /// Reference to a variable by name.
    Variable {
        /// Name of the variable.
        name: String,
        /// Line number in the source code.
        line: usize,
    },
    /// A unary operation (e.g. negation).
    UnaryOp {
        /// The unary operator to apply.
        op:   UnaryOperator,
        /// The operand expression.
        expr: Box<Self>,
        /// Line number in the source code.
        line: usize,
    },
    /// A binary operation (addition, subtraction, etc.).
    BinaryOp {
        /// Left operand.
        left:          Box<Self>,
        /// The operator.
        op:            BinaryOperator,
        /// Right operand.
        right:         Box<Self>,
        /// Line number in the source code.
        line:          usize,
        /// Optional relative tolerance for approximate comparisons.
        rel_tolerance: Option<f64>,
        /// Optional absolute tolerance for approximate comparisons.
        abs_tolerance: Option<f64>,
    },
    /// Function call expression (e.g. `sin(x)`).
    FunctionCall {
        /// Name of the function being called.
        name:      String,
        /// Arguments to the function.
        arguments: Vec<Self>,
        /// Line number in the source code.
        line:      usize,
    },
    /// Absolute value operation.
    Abs {
        /// The operand expression.
        expr: Box<Self>,
        /// Line number in the source code.
        line: usize,
    },
    /// Conditional ("if-then-else") expression.
    IfExpr {
        /// The primary condition expression.
        condition:   Box<Self>,
        /// Expression evaluated if the condition is true.
        then_branch: Box<Self>,
        /// Expression evaluated if the condition is false.
        else_branch: Option<Box<Self>>,
        /// Line number in the source code.
        line:        usize,
    },
    /// For-expression for ranged or iterator-based evaluation.
    ForExpr {
        /// Context for the for-expression (e.g., variable, range, body).
        context: ForExprContext,
        /// Line number in the source code.
        line:    usize,
    },
    /// A block containing multiple statements.
    Block {
        /// Statements inside the block.
        statements: Vec<Statement>,
        /// Line number in the source code.
        line:       usize,
    },
    /// Array literal expression.
    ArrayLiteral {
        /// Elements of the array.
        elements: Vec<Self>,
        /// Line number in the source code.
        line:     usize,
    },
    /// Array indexing expression (e.g., `arr[2]`).
    ArrayIndex {
        /// The array to index into.
        array: Box<Self>,
        /// The index to access.
        index: Box<Self>,
        /// Line number in the source code.
        line:  usize,
    },
    /// Norm (magnitude) operation.
    Norm {
        /// The expression whose norm is being taken.
        expr: Box<Self>,
        /// Line number in the source code.
        line: usize,
    },
    /// Set literal expression.
    SetLiteral {
        /// Elements of the set.
        elements: Vec<Self>,
        /// Line number in the source code.
        line:     usize,
    },
}

impl Expr {
    /// Gets the line number from `self`.
    /// ## Example
    /// ```
    /// use arithma::ast::Expr;
    ///
    /// let expr = Expr::Variable { name: "x".to_string(),
    ///                             line: 5, };
    ///
    /// assert_eq!(expr.line_number(), 5);
    /// ```
    #[must_use]
    pub const fn line_number(&self) -> usize {
        match self {
            Self::Literal { line, .. }
            | Self::Variable { line, .. }
            | Self::UnaryOp { line, .. }
            | Self::BinaryOp { line, .. }
            | Self::FunctionCall { line, .. }
            | Self::Abs { line, .. }
            | Self::IfExpr { line, .. }
            | Self::ForExpr { line, .. }
            | Self::Block { line, .. }
            | Self::ArrayLiteral { line, .. }
            | Self::ArrayIndex { line, .. }
            | Self::Norm { line, .. }
            | Self::SetLiteral { line, .. } => *line,
        }
    }
}

/// Represents a user-defined function definition.
///
/// A function binds a single parameter name to an expression body.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef {
    /// The name of the function.
    pub name:   String,
    /// The parameter names (e.g. `x`).
    pub params: Vec<String>,
    /// The body expression evaluated when the function is called.
    pub body:   Expr,
    /// Line number in the source code.
    pub line:   usize,
}

/// Represents a top-level statement.
///
/// Statements are the units parsed from input lines.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// A user-defined function declaration.
    Function(FunctionDef),
    /// A standalone expression evaluated for its result.
    Expression {
        /// The expression to evaluate.
        expr: Expr,
        /// Line number in the source code.
        line: usize,
    },
    /// A variable declaration using `let`.
    VariableDeclaration {
        /// The name of the variable.
        name:  String,
        /// The initial value of the variable.
        value: Expr,
        /// Line number in the source code.
        line:  usize,
    },
    /// A variable assignment binding a name to an expression.
    Assignment {
        /// The name of the variable.
        name:  String,
        /// The value which is being assigned.
        value: Expr,
        /// Line number in the source code.
        line:  usize,
    },
    /// A compound assignment consisting of a variable and an operation.
    CompoundAssignment {
        /// The name of the variable.
        name:  String,
        /// The binary operation (e.g., `+=`, `-=`, etc.).
        op:    BinaryOperator,
        /// The value to be combined with the current variable value.
        value: Expr,
        /// Line number in the source code.
        line:  usize,
    },
    /// Setting relative tolerance via `#[rel_tolerance()]`.
    SetRelTolerance(f64),
    /// Setting absolute tolerance via `#[abs_tolerance()]`.
    SetAbsTolerance(f64),
}

/// Represents a binary operator.
///
/// Binary operators include arithmetic and comparisons.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    /// Addition (`+`)
    Add,
    /// Subtraction (`-`)
    Sub,
    /// Multiplication (`*`)
    Mul,
    /// Division (`/`)
    Div,
    /// Exponentiation (`^`)
    Pow,
    /// Modulo (`%`)
    Mod,
    /// Less than (`<`)
    Less,
    /// Greater than (`>`)
    Greater,
    /// Less than or equal (`<=`)
    LessEqual,
    /// Greater than or equal (`>=`)
    GreaterEqual,
    /// Equal to (`==`)
    Equal,
    /// Not equal to (`!=`)
    NotEqual,
    /// Approximately equal to (`~`)
    ApproxEqual,
    /// Not approximately equal to (`!~`)
    NotApproxEqual,
    /// Logical exclusive or (`xor`)
    Xor,
    /// Logical and (`and`)
    And,
    /// Logical or (`or`)
    Or,
    /// Set intersection (`&`)
    Intersection,
    /// Symmetric difference (`(-)`)
    SymmDifference,
    /// Matrix multiplication (`@`)
    MatMul,
}
/// Represents a unary operator.
///
/// Unary operators include negation and logical NOT.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnaryOperator {
    /// Arithmetic negation (e.g. `-x`).
    Negate,
    /// Logical NOT (e.g. `!x`).
    Not,
    /// Factorial with optional repetition (e.g., `x!`, with the value
    /// indicating the number of factorial applications).
    Factorial(u8),
}

/// Context for a for-expression.
#[derive(Debug, Clone, PartialEq)]
pub struct ForExprContext {
    /// The loop variable name.
    pub var:       String,
    /// The starting expression for the loop range.
    pub start:     Box<Expr>,
    /// The end expression for the loop range (if present).
    pub end:       Option<Box<Expr>>,
    /// The body of the loop to be evaluated for each iteration.
    pub body:      Box<Expr>,
    /// Whether the end value is included in the range.
    pub inclusive: bool,
}

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinaryOperator::{
            Add, And, ApproxEqual, Div, Equal, Greater, GreaterEqual, Intersection, Less,
            LessEqual, MatMul, Mod, Mul, NotApproxEqual, NotEqual, Or, Pow, Sub, SymmDifference,
            Xor,
        };
        let operator = match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Pow => "^",
            Mod => "%",
            Less => "<",
            Greater => ">",
            LessEqual => "<=",
            GreaterEqual => ">=",
            Equal => "==",
            NotEqual => "!=",
            ApproxEqual => "~",
            NotApproxEqual => "!~",
            Xor => "xor",
            And => "and",
            Or => "or",
            Intersection => "&",
            SymmDifference => "(-)",
            MatMul => "@",
        };
        write!(f, "{operator}")
    }
}
