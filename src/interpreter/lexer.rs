use logos::Logos;

/// Represents a lexical token in the source input.
/// A token is a minimal but meaningful unit of text produced by the lexer.
/// This enum defines all recognized tokens in the language.
#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(extras = LexerExtras)]
pub enum Token {
    /// Numeric literal tokens, such as `3.14`, `.5`, `2.0` or `2.1e-10`.
    #[regex(r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?", parse_float)]
    #[regex(r"\.[0-9]+([eE][+-]?[0-9]+)?", parse_float)]
    #[regex(r"[0-9]+[eE][+-]?[0-9]+", parse_float)]
    Real(f64),
    /// Integer literal tokens, such as `42`.
    #[regex(r"[0-9]+", parse_integer)]
    Integer(i64),
    /// Boolean literal tokens, such as `true`.
    #[token("true", parse_bool)]
    #[token("false", parse_bool)]
    Bool(bool),
    /// `do`
    #[token("do")]
    Do,
    /// `(-)`
    #[regex(r"\(-\)")]
    OMinus,
    /// `&`
    #[token("&")]
    Ampersand,
    /// `xor`
    #[token("xor")]
    Xor,
    /// `and`
    #[token("and")]
    And,
    /// `or`
    #[token("or")]
    Or,
    /// `let`
    #[token("let")]
    Let,
    /// Identifier tokens; variable or function names such as `x` or `square`.
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Identifier(String),
    /// `// Comments.`
    #[regex(r"//[^\n\r]*", logos::skip, allow_greedy = true)]
    Comment,
    /// ```
    /// // Multi line comments.
    /// ```
    #[regex(r"/\*([^*]|\*[^/])*\*/", |lex| {
        let comment      = lex.slice();
        let newlines     = comment.chars().filter(|&c| c == '\n').count();
        lex.extras.line += newlines;
        logos::Skip
    })]
    MultiLineComment,
    /// `for`
    #[token("for")]
    For,
    /// `in`
    #[token("in")]
    In,
    /// `..=`
    #[token("..=")]
    DotDotEq,
    /// `..`
    #[token("..")]
    DotDot,
    /// `if`
    #[token("if")]
    If,
    /// `else`
    #[token("else")]
    Else,
    /// `+=`
    #[token("+=")]
    PlusAssign,
    /// `-=`
    #[token("-=")]
    MinusAssign,
    /// `*=`
    #[token("*=")]
    MulAssign,
    /// `/=`
    #[token("/=")]
    DivAssign,
    /// `@`
    #[token("@")]
    At,
    /// `+`
    #[token("+")]
    Plus,
    /// `-`
    #[token("-")]
    Minus,
    /// `*`
    #[token("*")]
    Star,
    /// `/`
    #[token("/")]
    Slash,
    /// `^`
    #[token("^")]
    Caret,
    /// `%`
    #[token("%")]
    Percent,
    /// `(`
    #[token("(")]
    LParen,
    /// `)`
    #[token(")")]
    RParen,
    /// `=`
    #[token("=")]
    Equals,
    /// `||`
    #[token("||")]
    DoublePipe,
    /// `|`
    #[token("|")]
    Pipe,
    /// `{`
    #[token("{")]
    LBrace,
    /// `}`
    #[token("}")]
    RBrace,
    /// `[`
    #[token("[")]
    LBracket,
    /// `]`
    #[token("]")]
    RBracket,
    /// `,`
    #[token(",")]
    Comma,
    /// `==`
    #[token("==")]
    EqualEqual,
    /// `!=`
    #[token("!=")]
    BangEqual,
    /// `<=`
    #[token("<=")]
    LessEqual,
    /// `>=`
    #[token(">=")]
    GreaterEqual,
    /// `<`
    #[token("<")]
    Less,
    /// `>`
    #[token(">")]
    Greater,
    /// `!`
    #[token("!")]
    Bang,
    /// `~`
    #[token("~")]
    Tilde,
    /// `!~`
    #[token("!~")]
    BangTilde,
    /// `#`
    #[token("#")]
    Hash,

    /// Unrecognized characters.
    #[token("\n", |lex| {
        lex.extras.line += 1;
        Token::NewLine
    })]
    NewLine,
    /// Tabs and feeds.
    #[regex(r"[ \t\f]+", logos::skip)]
    Ignored,
}

/// Additional information carried by the lexer during tokenization.
///
/// Tracks the current line number for error reporting and diagnostics.
/// Automatically resets or increments as newlines are processed.
#[derive(Default)]
pub struct LexerExtras {
    /// The current line number in the source being tokenized.
    pub line: usize,
}

/// Parses a floating-point literal from the current token slice.
///
/// # Parameters
/// - `lex`: Reference to the Logos lexer at the current token.
///
/// # Returns
/// - `Some(f64)`: The parsed floating-point value if successful.
/// - `None`: If the token slice is not a valid float.
fn parse_float(lex: &logos::Lexer<Token>) -> Option<f64> {
    lex.slice().parse().ok()
}
/// Parses an integer literal from the current token slice.
///
/// # Parameters
/// - `lex`: Reference to the Logos lexer at the current token.
///
/// # Returns
/// - `Some(i64)`: The parsed integer value if successful.
/// - `None`: If the token slice is not a valid integer.
fn parse_integer(lex: &logos::Lexer<Token>) -> Option<i64> {
    lex.slice().parse().ok()
}
/// Parses a boolean literal from the current token slice (`true` or `false`).
///
/// # Parameters
/// - `lex`: Reference to the Logos lexer at the current token.
///
/// # Returns
/// - `Some(true)` if the slice is `"true"`.
/// - `Some(false)` if the slice is `"false"`.
/// - `None` otherwise.
fn parse_bool(lex: &logos::Lexer<Token>) -> Option<bool> {
    match lex.slice() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}
