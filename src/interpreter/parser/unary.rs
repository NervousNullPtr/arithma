use std::iter::Peekable;

use crate::{
    ast::{Expr, ForExprContext, UnaryOperator},
    error::ParseError,
    interpreter::{
        evaluator::utils::is_reserved_identifier,
        lexer::Token,
        parser::{
            block::parse_block,
            core::{ParseResult, parse_expression, parse_if},
            utils::{parse_comma_separated, parse_set_literal},
        },
        value::complex::ComplexNumber,
    },
    util::num::i64_to_f64_checked,
};

/// Parses a unary expression.
///
/// Supports prefix operators:
/// - `-`  (numeric negation)
/// - `!`  (logical not)
///
/// Unary operators are right-associative, so an input like `!-x` is parsed as
/// `!( -x )`.
///
/// If no unary operator is present, the function delegates to
/// [`parse_primary`] and then applies any postfix operators via
/// [`parse_postfix`].
///
/// Grammar:
/// ```text
///     unary := ("-" | "!") unary
///            | primary postfix*
/// ```
/// # Parameters
/// - `tokens`: Token iterator with lookahead.
///
/// # Returns
/// An [`Expr::UnaryOp`] or a primary expression possibly followed by postfixes.
pub(crate) fn parse_unary<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    if let Some((Token::Minus, line)) = tokens.peek() {
        tokens.next();
        let expr = parse_unary(tokens)?;
        Ok(Expr::UnaryOp { op:   UnaryOperator::Negate,
                           expr: Box::new(expr),
                           line: *line, })
    } else if let Some((Token::Bang, line)) = tokens.peek() {
        tokens.next();
        let expr = parse_unary(tokens)?;
        Ok(Expr::UnaryOp { op:   UnaryOperator::Not,
                           expr: Box::new(expr),
                           line: *line, })
    } else {
        let primary = parse_primary(tokens)?;
        parse_postfix(tokens, primary)
    }
}

/// Parses a primary (atomic) expression.
///
/// Primary expressions form the base of the expression grammar and include:
/// - numeric and boolean literals
/// - identifiers
/// - function calls
/// - parenthesized expressions
/// - absolute expressions (`|expr|`)
/// - norm expressions (`||expr||`)
/// - set literals (`{ ... }`)
/// - array literals (`[ ... ]`)
/// - `do` blocks
/// - `if` expressions
/// - `for` expressions
///
/// This function does not handle unary operators or postfix operators.
/// It dispatches to specialized parsing functions depending on the leading
/// token.
///
/// Grammar (simplified):
/// ```text
///     primary := literal
///              | identifier_or_function
///              | "(" expression ")"
///              | "|" expression "|"
///              | "||" expression "||"
///              | "[" elements "]"
///              | "{" elements "}"
///              | do_block
///              | if_expression
///              | for_expression
/// ```
/// # Parameters
/// - `tokens`: Token iterator positioned at the start of a primary expression.
///
/// # Returns
/// The parsed primary [`Expr`] or a `ParseError` on failure.
pub(crate) fn parse_primary<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let peeked = tokens.peek()
                       .ok_or(ParseError::UnexpectedEndOfInput { line: 0 })?;

    match peeked {
        (Token::Real(..) | Token::Integer(..) | Token::Bool(..), _) => parse_literal(tokens),
        (Token::DoublePipe, _) => parse_norm(tokens),
        (Token::Pipe, _) => parse_abs(tokens),
        (Token::LParen, _) => parse_grouping(tokens),
        (Token::Do, _) => parse_do_block(tokens),
        (Token::LBrace, _) => parse_set_literal(tokens),
        (Token::LBracket, _) => parse_array_literal(tokens),
        (Token::If, _) => parse_if_expression(tokens),
        (Token::For, _) => parse_for_expression(tokens),
        (Token::Identifier(_), _) => parse_identifier_or_function(tokens),
        (tok, line) => Err(ParseError::UnexpectedToken { token: format!("{tok:?}"),
                                                         line:  *line, }),
    }
}

/// Parses postfix operators applied to an expression.
///
/// This function is called after parsing a primary or unary expression and
/// handles two kinds of postfix constructs:
///
/// 1. **Array indexing** expr[ index ]
///
///    Multiple chained indices are allowed:
/// ```text
///        a[0][1]
/// ```
/// 2. **Factorials and multi-factorials**
/// ```text
///        expr!
///        expr!!
///        expr!!!
/// ```
///    Factorials are counted and converted into a single
///    `UnaryOperator::Factorial(n)` node. Overflow in the factorial count
///    produces a `ParseError::TooManyFactorials`.
///
/// Parsing continues until no further postfix operator is found.
///
/// Grammar:
/// ```text
///     postfix := primary
///              | postfix "[" expression "]"
///              | postfix "!"*
/// ```
/// # Parameters
/// - `tokens`: Token iterator after a primary/unary expression.
/// - `node`: The expression to which postfix operators will be applied.
///
/// # Returns
/// An updated [`Expr`] with all postfix operators folded in.
///
/// # Errors
/// Returns a `ParseError` if:
/// - an `[` is not properly closed with `]`,
/// - factorial count overflows `u8`,
/// - the index expression fails to parse.
fn parse_postfix<'a, I>(tokens: &mut Peekable<I>, mut node: Expr) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    loop {
        // Array indexing.
        if let Some((Token::LBracket, index_line)) = tokens.peek() {
            tokens.next();
            let index = parse_expression(tokens)?;
            match tokens.next() {
                Some((Token::RBracket, _)) => {
                    node = Expr::ArrayIndex { array: Box::new(node),
                                              index: Box::new(index),
                                              line:  *index_line, };
                },
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        token: "Expected ']' after array index.".to_string(),
                        line: *index_line,
                    });
                },
            }
            continue;
        }
        let mut factorial_count = 0u8;
        while let Some((Token::Bang, _)) = tokens.peek() {
            tokens.next();
            factorial_count = factorial_count.checked_add(1).ok_or_else(|| {
                                                                 ParseError::TooManyFactorials {
                        count: factorial_count + 1,
                        line: node.line_number(),
                    }
                                                             })?;
        }
        if factorial_count > 0 {
            node = Expr::UnaryOp { op:   UnaryOperator::Factorial(factorial_count),
                                   expr: Box::new(node.clone()),
                                   line: node.line_number(), };
            continue;
        }
        break;
    }
    Ok(node)
}

/// Parses a numeric or boolean literal.
///
/// Supported forms include:
/// - Integer literals
/// - Real literals
/// - Boolean literals (`true`, `false`)
/// - Complex literals using an imaginary suffix: `3i`
///
/// Only `i` and `j` are accepted as imaginary-unit identifiers.
/// A literal followed by an unexpected identifier results in a parse error.
///
/// Grammar (simplified):
/// ```text
///     literal := INTEGER [("i" | "j")]?
///               | REAL    [("i" | "j")]?
///               | BOOL
/// ```
/// Complex literals are converted into:
/// ```text
///     LiteralValue::Complex(real = 0.0, imag = number)
/// ```
/// # Parameters
/// - `tokens`: Token iterator positioned at a literal.
///
/// # Returns
/// An [`Expr::Literal`] containing the parsed value.
///
/// # Errors
/// Returns a `ParseError` if:
/// - an unexpected identifier follows the literal,
/// - an integer literal used for a complex value overflows during conversion.
fn parse_literal<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (tok, line) = tokens.peek().unwrap();
    match tok {
        Token::Real(n) => {
            tokens.next();
            if let Some((Token::Identifier(id), _)) = tokens.peek() {
                if id == "i" || id == "j" {
                    tokens.next();
                    Ok(Expr::Literal { value: (0.0, *n).into(),
                                       line:  *line, })
                } else {
                    Err(ParseError::UnexpectedToken { token: id.to_owned(),
                                                      line:  *line, })
                }
            } else {
                Ok(Expr::Literal { value: n.into(),
                                   line:  *line, })
            }
        },
        Token::Integer(n) => {
            tokens.next();
            if let Some((Token::Identifier(id), _)) = tokens.peek() {
                if id == "i" || id == "j" {
                    tokens.next();
                    Ok(Expr::Literal {
                        value: (
                            0.0,
                            i64_to_f64_checked(*n, ParseError::LiteralTooLarge { line: *line })?,
                        )
                            .into(),
                        line: *line,
                    })
                } else {
                    Err(ParseError::UnexpectedToken { token: id.to_owned(),
                                                      line:  *line, })
                }
            } else {
                Ok(Expr::Literal { value: n.into(),
                                   line:  *line, })
            }
        },
        Token::Bool(b) => {
            tokens.next();
            Ok(Expr::Literal { value: b.into(),
                               line:  *line, })
        },
        _ => unreachable!(),
    }
}

/// Parses a norm expression of the form `|| expression ||`.
///
/// The function consumes the opening `||`, parses an expression, and expects a
/// closing `||`. Missing closing delimiters produce
/// `ParseError::ExpectedDoublePipe`.
///
/// Grammar: `norm := "||" expression "||"`
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `||`.
///
/// # Returns
/// An [`Expr::Norm`] node.
fn parse_norm<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = *tokens.next().unwrap();
    let expr = parse_expression(tokens)?;
    match tokens.next() {
        Some((Token::DoublePipe, _)) => Ok(Expr::Norm { expr: Box::new(expr),
                                                        line }),
        _ => Err(ParseError::ExpectedDoublePipe { line }),
    }
}

/// Parses an absolute-value expression of the form `| expression |`.
///
/// The function consumes the opening `|`, parses an expression, and expects a
/// closing `|`. Missing closing delimiters produce `ParseError::ExpectedPipe`.
///
/// Grammar: `abs := "|" expression "|"`
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `|`.
///
/// # Returns
/// An [`Expr::Abs`] node.
fn parse_abs<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = *tokens.next().unwrap();
    let expr = parse_expression(tokens)?;
    match tokens.next() {
        Some((Token::Pipe, _)) => Ok(Expr::Abs { expr: Box::new(expr),
                                                 line }),
        _ => Err(ParseError::ExpectedPipe { line }),
    }
}

/// Parses a parenthesized expression.
///
/// Expected form `( expression )`
///
/// The function consumes the opening parenthesis, parses the enclosed
/// expression, and then requires a closing `)`. Failure to find the closing
/// parenthesis yields `ParseError::ExpectedClosingParen`.
///
/// Grammar `grouping := "(" expression ")"`
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `(`.
///
/// # Returns
/// The inner expression as-is (no wrapper node).
fn parse_grouping<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = *tokens.next().unwrap();
    let expr = parse_expression(tokens)?;
    match tokens.next() {
        Some((Token::RParen, _)) => Ok(expr),
        _ => Err(ParseError::ExpectedClosingParen { line }),
    }
}

/// Parses a `do { ... }` block expression.
///
/// Expected structure: `do { statements }`
///
/// The function consumes the `do` keyword, requires a `{`, and then delegates
/// to `parse_block` to parse the inner statements until the matching `}`.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `do`.
///
/// # Returns
/// An [`Expr::Block`] representing the parsed block.
///
/// # Errors
/// Returns a `ParseError` if:
/// - `do` is missing,
/// - `{` does not follow `do`,
/// - the block is malformed or ends unexpectedly.
pub fn parse_do_block<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, do_line) = match tokens.next() {
        Some((Token::Do, line)) => (Token::Do, line),
        Some((tok, line)) => {
            return Err(ParseError::UnexpectedToken { token: format!("Expected 'do', found {tok:?}"),
                                                     line:  *line, });
        },
        None => {
            return Err(ParseError::UnexpectedEndOfInput { line: 0 });
        },
    };

    let line = match tokens.next() {
        Some((Token::LBrace, line)) => line,
        Some((tok, line)) => {
            return Err(ParseError::UnexpectedToken { token: format!("Expected '{{' after 'do', found {tok:?}"),
                                                     line:  *line, });
        },
        None => {
            return Err(ParseError::UnexpectedEndOfInput { line: *do_line });
        },
    };

    parse_block(tokens, *line)
}

/// Parses an array literal of the form `[expr1, expr2, ..., exprN]`.
///
/// Elements are parsed using `parse_expression`, separated by commas.
/// Trailing commas are allowed or disallowed depending on
/// `parse_comma_separated`.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `[`
///
/// # Returns
/// An [`Expr::ArrayLiteral`] node containing the parsed elements.
///
/// # Errors
/// Returns a `ParseError` if:
/// - elements cannot be parsed,
/// - the closing `]` is missing.
fn parse_array_literal<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = tokens.next().unwrap();
    let elements = parse_comma_separated(tokens, parse_expression, &Token::RBracket)?;
    Ok(Expr::ArrayLiteral { elements,
                            line: *line })
}

/// Parses an `if` expression.
///
/// This consumes the `if` keyword and delegates to `parse_if`, which handles
/// the full grammar including `else` and chained `else if` constructs.
///
/// Example form:
/// ```text
///     if condition do { ... }
///     else do { ... }
/// ```
/// # Parameters
/// - `tokens`: Token iterator positioned at `if`.
///
/// # Returns
/// An [`Expr::IfExpr`] node.
fn parse_if_expression<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = tokens.next().unwrap();
    parse_if(tokens, *line)
}

/// Parses a `for` expression.
///
/// Supported forms:
///
/// - for x in start .. end     do { ... }
/// - for x in start ..= end    do { ... }
/// - for x in array            do { ... }
///
/// The loop variable must not be reserved.
/// Depending on the range operator, the `end` expression may be present or
/// absent.
///
/// The body must be introduced with `do` and is parsed using
/// [`parse_do_block`].
///
/// # Parameters
/// - `tokens`: Token iterator positioned at `for`.
///
/// # Returns
/// An [`Expr::ForExpr`] containing a [`ForExprContext`].
///
/// # Errors
/// Returns a `ParseError` if:
/// - the loop variable is missing or reserved,
/// - `in` is missing,
/// - the range operator is invalid,
/// - the `do` keyword is missing,
/// - the body or expressions fail to parse.
fn parse_for_expression<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = *tokens.next().unwrap();

    let var = match tokens.next() {
        Some((Token::Identifier(name), _)) => name.clone(),
        _ => {
            return Err(ParseError::UnexpectedToken { token:
                                                         "Expected loop variable".to_string(),
                                                     line });
        },
    };

    if is_reserved_identifier(&var) {
        return Err(ParseError::IdentifierReserved { name: var, line });
    }

    match tokens.next() {
        Some((Token::In, _)) => {},
        _ => {
            return Err(ParseError::UnexpectedToken {
                token: "Expected 'in' after loop variable".to_string(),
                line,
            });
        },
    }
    let start = parse_unary(tokens)?;
    let (inclusive, end) = match tokens.peek() {
        Some((Token::DotDot, _)) => {
            tokens.next();

            (false, Some(Box::new(parse_expression(tokens)?)))
        },
        Some((Token::DotDotEq, _)) => {
            tokens.next();

            (true, Some(Box::new(parse_expression(tokens)?)))
        },
        Some((Token::Do, _)) => (false, None),
        other => {
            let found = match other {
                Some((tok, _)) => format!("{tok:?}"),
                None => "end of input".to_string(),
            };
            return Err(ParseError::UnexpectedToken { token: format!("Expected '..', '..=', or '{{', found {found}"),
                                                     line });
        },
    };

    match tokens.peek() {
        Some((Token::Do, _)) => {},
        _ => {
            return Err(ParseError::UnexpectedToken { token:
                                                         "Expected 'do' after for range".to_string(),
                                                     line });
        },
    }

    let body = parse_do_block(tokens)?;

    Ok(Expr::ForExpr { context: ForExprContext { var,
                                                 start: Box::new(start),
                                                 end,
                                                 body: Box::new(body),
                                                 inclusive },
                       line })
}

/// Parses an identifier, imaginary unit, or function call.
///
/// Supported forms:
///
/// - identifier
/// - identifier(arg1, arg2, ...)
/// - i   // imaginary unit
/// - j   // imaginary unit
///
/// The function first consumes the identifier token.
/// If the next token is `(`, a function-call expression is parsed.
/// If the identifier is `i` or `j`, it is treated as a complex literal with
/// value `0 + 1i`.
/// Otherwise, it is parsed as a variable reference.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at an identifier.
///
/// # Returns
/// - [`Expr::FunctionCall`] if followed by parentheses,
/// - [`Expr::Literal`] for `i` or `j`,
/// - [`Expr::Variable`] otherwise.
///
/// # Errors
/// Returns a `ParseError` if:
/// - the initial token is not an identifier,
/// - function-call arguments fail to parse,
/// - the closing `)` is missing.
fn parse_identifier_or_function<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (name, line) = match tokens.next() {
        Some((Token::Identifier(n), line)) => (n.clone(), line),
        Some((tok, line)) => {
            return Err(ParseError::UnexpectedToken { token: format!("{tok:?}"),
                                                     line:  *line, });
        },
        None => {
            return Err(ParseError::UnexpectedEndOfInput { line: 0 });
        },
    };

    match tokens.peek() {
        Some((Token::LParen, _)) => {
            tokens.next();
            let args = parse_comma_separated(tokens, parse_expression, &Token::RParen)?;
            Ok(Expr::FunctionCall { name,
                                    arguments: args,
                                    line: *line })
        },
        _ if name == "i" || name == "j" => {
            Ok(Expr::Literal { value: ComplexNumber::new(0.0, 1.0).into(),
                               line:  *line, })
        },
        _ => Ok(Expr::Variable { name, line: *line }),
    }
}
