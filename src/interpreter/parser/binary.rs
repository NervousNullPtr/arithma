use std::iter::Peekable;

use crate::{
    ast::{BinaryOperator, Expr},
    error::ParseError,
    interpreter::{
        lexer::Token,
        parser::{core::ParseResult, unary::parse_unary},
    },
    util::num::i64_to_f64_checked,
};

/// Parses addition and subtraction expressions.
///
/// Handles left-associative binary operators: `+` and `-`.
///
/// The rule is: `additive := multiplicative (("+" | "-") multiplicative)*`
///
/// # Parameters
/// - `tokens`: Token stream with line information.
///
/// # Returns
/// An `Expr::BinaryOp` tree representing the parsed expression.
pub fn parse_additive<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_multiplicative(tokens)?;
    loop {
        if let Some((token, line)) = tokens.peek()
           && let Some(op) = token_to_binary_operator(token)
           && matches!(op, BinaryOperator::Add | BinaryOperator::Sub)
        {
            tokens.next();
            let right = parse_multiplicative(tokens)?;
            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line: *line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };
            continue;
        }
        break;
    }
    Ok(left)
}

/// Parses multiplication-level expressions.
///
/// Handles left-associative operators:
/// `*`, `/`, `%`, `&`, `(-)`, and matrix multiplication `@`.
///
/// The rule is: ` multiplicative := exponent (("*" | "/" | "%" | "&" | "(-)" |
/// "@") exponent)*`
///
/// # Parameters
/// - `tokens`: Token stream with line information.
///
/// # Returns
/// A binary expression tree combining exponent-level nodes.
pub fn parse_multiplicative<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_exponent(tokens)?;
    loop {
        if let Some((token, line)) = tokens.peek()
           && let Some(op) = token_to_binary_operator(token)
           && matches!(op,
                       BinaryOperator::Mul
                       | BinaryOperator::Div
                       | BinaryOperator::Mod
                       | BinaryOperator::Intersection
                       | BinaryOperator::SymmDifference
                       | BinaryOperator::MatMul)
        {
            tokens.next();
            let right = parse_exponent(tokens)?;
            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line: *line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };
            continue;
        }
        break;
    }
    Ok(left)
}

/// Parses exponentiation expressions.
///
/// Handles repeated exponentiation with right-associativity:
/// `a ^ b ^ c` parses as `a ^ (b ^ c)`.
///
/// The rule is: `exponent := unary ("^" unary)*`
///
/// # Parameters
/// - `tokens`: Token stream.
///
/// # Returns
/// An exponentiation expression tree.
pub fn parse_exponent<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_unary(tokens)?;
    while let Some((token, line)) = tokens.peek() {
        if let Some(op) = token_to_binary_operator(token)
           && matches!(op, BinaryOperator::Pow)
        {
            tokens.next();
            let right = parse_unary(tokens)?;
            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line: *line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };
            continue;
        }
        break;
    }
    Ok(left)
}

/// Parses relational and equality operators.
///
/// This parser handles all comparison operators:
/// `<`, `>`, `<=`, `>=`, `==`, `!=`, `~`, `!~`.
///
/// For approximate operators (`~`, `!~`), optional tolerance arguments
/// may follow the right-hand operand:
///
/// ```text
/// a ~ b,  <rel_tolerance>
/// a ~ b,  <rel_tolerance>, abs = <abs_tolerance>
/// a ~ b,  abs = <abs_tolerance>
/// ```
///
/// Tolerances must be numeric. Integer tolerances are promoted safely to `f64`.
///
/// # Parameters
/// - `tokens`: Token stream (token + line number) wrapped in a `Peekable`.
///
/// # Returns
/// A possibly nested `Expr::BinaryOp` tree with optional tolerance fields.
pub fn parse_relational<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_additive(tokens)?;

    while let Some((token, line)) = tokens.peek() {
        let op = match token_to_binary_operator(token) {
            Some(op) if is_relational_op(op) => op,
            _ => break,
        };

        let line = *line;
        tokens.next(); // consume operator

        let right = parse_additive(tokens)?;
        let (rel_tolerance, abs_tolerance) = if is_approx_op(op) {
            parse_approx_tolerances(tokens, line)?
        } else {
            (None, None)
        };

        left = Expr::BinaryOp { left: Box::new(left),
                                op,
                                right: Box::new(right),
                                line,
                                rel_tolerance,
                                abs_tolerance };
    }

    Ok(left)
}

/// Maps a token to its corresponding binary operator.
///
/// Returns `Some(BinaryOperator)` when the token represents a binary operator
/// (`+`, `-`, `*`, `/`, `%`, `^`, comparison operators, logical operators,
/// set operators, approximate-equality operators, and matrix multiplication).
/// Returns `None` for all other tokens.
///
/// should be parsed as a `BinaryOp`.
///
/// # Parameters
/// - `token`: Token to convert.
///
/// # Returns
/// `Some(BinaryOperator)` if the token corresponds to a binary operator,
/// otherwise `None`.
///
/// # Example
/// ```
/// use arithma::{
///     ast::BinaryOperator,
///     interpreter::{lexer::Token, parser::binary::token_to_binary_operator},
/// };
///
/// assert_eq!(token_to_binary_operator(&Token::Plus),
///            Some(BinaryOperator::Add));
/// ```
#[must_use]
pub const fn token_to_binary_operator(token: &Token) -> Option<BinaryOperator> {
    match token {
        Token::Plus => Some(BinaryOperator::Add),
        Token::Minus => Some(BinaryOperator::Sub),
        Token::Star => Some(BinaryOperator::Mul),
        Token::Slash => Some(BinaryOperator::Div),
        Token::Percent => Some(BinaryOperator::Mod),
        Token::Caret => Some(BinaryOperator::Pow),
        Token::Less => Some(BinaryOperator::Less),
        Token::Greater => Some(BinaryOperator::Greater),
        Token::LessEqual => Some(BinaryOperator::LessEqual),
        Token::GreaterEqual => Some(BinaryOperator::GreaterEqual),
        Token::EqualEqual => Some(BinaryOperator::Equal),
        Token::BangEqual => Some(BinaryOperator::NotEqual),
        Token::Tilde => Some(BinaryOperator::ApproxEqual),
        Token::BangTilde => Some(BinaryOperator::NotApproxEqual),
        Token::Xor => Some(BinaryOperator::Xor),
        Token::And => Some(BinaryOperator::And),
        Token::Or => Some(BinaryOperator::Or),
        Token::Ampersand => Some(BinaryOperator::Intersection),
        Token::OMinus => Some(BinaryOperator::SymmDifference),
        Token::At => Some(BinaryOperator::MatMul),
        _ => None,
    }
}

/// Parses logical AND expressions.
///
/// Handles left-associative chains of `&&` (or whatever token maps to
/// `BinaryOperator::And`).
/// Precedence is higher than XOR and OR.
///
/// Grammar: `and := relational ("and" relational)*`
///
/// # Parameters
/// - `tokens`: Token iterator providing `(Token, line)` pairs.
///
/// # Returns
/// A binary expression tree with `BinaryOperator::And` nodes.
pub fn parse_logical_and<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_relational(tokens)?;

    loop {
        if let Some((token, line)) = tokens.peek()
           && let Some(op) = token_to_binary_operator(token)
           && matches!(op, BinaryOperator::And)
        {
            let line = *line;
            tokens.next();

            let right = parse_relational(tokens)?;

            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };

            continue;
        }

        break;
    }

    Ok(left)
}

/// Parses logical OR expressions.
///
/// Handles left-associative chains of OR operators.
/// Precedence is lower than XOR and AND.
///
/// Grammar: `logical or := xor ("or" xor)*`
///
/// # Parameters
/// - `tokens`: Token iterator with lookahead.
///
/// # Returns
/// A binary expression tree using `BinaryOperator::Or`.
pub fn parse_logical_or<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_logical_xor(tokens)?;

    loop {
        if let Some((token, line)) = tokens.peek()
           && let Some(op) = token_to_binary_operator(token)
           && matches!(op, BinaryOperator::Or)
        {
            let line = *line;
            tokens.next();

            let right = parse_logical_xor(tokens)?;

            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };
            continue;
        }

        break;
    }

    Ok(left)
}

/// Parses logical XOR expressions.
///
/// Handles left-associative chains of XOR operators.
/// Precedence is between AND and OR.
///
/// Grammar: `xor := and ("xor" and)*`
///
/// # Parameters
/// - `tokens`: Token iterator with lookahead.
///
/// # Returns
/// A binary expression tree using `BinaryOperator::Xor`.
pub fn parse_logical_xor<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut left = parse_logical_and(tokens)?;

    loop {
        if let Some((token, line)) = tokens.peek()
           && let Some(op) = token_to_binary_operator(token)
           && matches!(op, BinaryOperator::Xor)
        {
            let line = *line;
            tokens.next();

            let right = parse_logical_and(tokens)?;

            left = Expr::BinaryOp { left: Box::new(left),
                                    op,
                                    right: Box::new(right),
                                    line,
                                    rel_tolerance: None,
                                    abs_tolerance: None };
            continue;
        }

        break;
    }

    Ok(left)
}

/// Determines whether a binary operator belongs to the relational class.
///
/// Supported categories:
/// - Strict relations: `<`, `>`
/// - Non-strict relations: `<=`, `>=`
/// - Equality: `==`, `!=`
/// - Approximate equality: `~`, `!~`
///
/// # Example
/// ```
/// use arithma::{ast::BinaryOperator, interpreter::parser::binary::is_relational_op};
///
/// assert!(is_relational_op(BinaryOperator::Less));
/// assert!(is_relational_op(BinaryOperator::ApproxEqual));
/// assert!(!is_relational_op(BinaryOperator::Add));
/// ```
#[must_use]
pub const fn is_relational_op(op: BinaryOperator) -> bool {
    matches!(op,
             BinaryOperator::Less
             | BinaryOperator::Greater
             | BinaryOperator::LessEqual
             | BinaryOperator::GreaterEqual
             | BinaryOperator::Equal
             | BinaryOperator::NotEqual
             | BinaryOperator::ApproxEqual
             | BinaryOperator::NotApproxEqual)
}

/// Returns `true` when the operator is approximate (`~` or `!~`).
///
/// # Example
/// ```
/// use arithma::{ast::BinaryOperator, interpreter::parser::binary::is_approx_op};
///
/// assert!(is_approx_op(BinaryOperator::ApproxEqual));
/// assert!(is_approx_op(BinaryOperator::NotApproxEqual));
/// assert!(!is_approx_op(BinaryOperator::Equal));
/// ```
#[must_use]
pub const fn is_approx_op(op: BinaryOperator) -> bool {
    matches!(op,
             BinaryOperator::ApproxEqual | BinaryOperator::NotApproxEqual)
}

/// Parses optional tolerance arguments for approximate comparisons.
///
/// The grammar allows these forms:
///
/// ```text
/// <nothing>
/// , <rel>
/// , <rel>, abs = <abs>
/// , abs = <abs>
/// ```
///
/// Both tolerance values are numeric. Integers are converted safely to `f64`.
///
/// # Errors
/// - Unexpected token in tolerance position.
/// - Missing numeric literal.
/// - Missing `=` after `abs`.
/// - Unexpected end of input.
///
/// # Returns
/// `(rel_tolerance, abs_tolerance)`
pub fn parse_approx_tolerances<'a, I>(tokens: &mut Peekable<I>,
                                      line: usize)
                                      -> ParseResult<(Option<f64>, Option<f64>)>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut rel_tol = None;
    let mut abs_tol = None;

    if let Some((Token::Comma, _)) = tokens.peek() {
        tokens.next(); // consume ','

        match tokens.peek() {
            // rel_tolerance first
            Some((Token::Real(_) | Token::Integer(_), _)) => {
                rel_tol = Some(parse_numeric(tokens, line)?);

                // Optional ", abs = x"
                if let Some((Token::Comma, _)) = tokens.peek() {
                    tokens.next();
                    abs_tol = Some(parse_abs_assignment(tokens, line)?);
                }
            },

            // abs = x (no rel tolerance)
            Some((Token::Identifier(id), _)) if id == "abs" => {
                abs_tol = Some(parse_abs_assignment(tokens, line)?);
            },

            Some((tok, l)) => {
                return Err(ParseError::UnexpectedToken { token: format!("Expected numeric tolerance or 'abs', found {tok:?}"),
                                                         line:  *l, });
            },

            None => return Err(ParseError::UnexpectedEndOfInput { line }),
        }
    }

    Ok((rel_tol, abs_tol))
}

/// Parses a numeric literal (`Real` or `Integer`) and returns it as `f64`.
///
/// Integer values are promoted using `i64_to_f64_checked`, preserving your
/// overflow-safety guarantees.
pub fn parse_numeric<'a, I>(tokens: &mut Peekable<I>, line: usize) -> ParseResult<f64>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    match tokens.next() {
        Some((Token::Real(v), _)) => Ok(*v),

        Some((Token::Integer(v), _)) => {
            i64_to_f64_checked(*v, ParseError::LiteralTooLarge { line })
        },

        Some((tok, l)) => {
            Err(ParseError::UnexpectedToken { token: format!("Expected numeric value, found {tok:?}"),
                                              line:  *l, })
        },

        None => Err(ParseError::UnexpectedEndOfInput { line }),
    }
}

/// Parses an absolute-tolerance assignment: `abs = <number>`.
///
/// The syntax is strict:
///
/// ```text
/// abs = 1e-12
/// ```
///
/// No whitespace-sensitive variants or reversed forms are allowed.
/// All values must be numeric.
///
/// # Errors
/// - Missing `abs` identifier.
/// - Missing `=`.
/// - Missing or invalid numeric literal.
pub fn parse_abs_assignment<'a, I>(tokens: &mut Peekable<I>, line: usize) -> ParseResult<f64>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    match tokens.next() {
        Some((Token::Identifier(id), _)) if id == "abs" => {},
        Some((tok, l)) => {
            return Err(ParseError::UnexpectedToken { token: format!("Expected 'abs', found {tok:?}"),
                                                     line:  *l, });
        },
        None => return Err(ParseError::UnexpectedEndOfInput { line }),
    }

    match tokens.next() {
        Some((Token::Equals, _)) => {},
        other => {
            return Err(ParseError::UnexpectedToken { token: format!("Expected '=' after 'abs', found {other:?}"),
                                                     line });
        },
    }

    parse_numeric(tokens, line)
}
