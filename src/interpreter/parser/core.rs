use std::iter::Peekable;

use crate::{
    ast::Expr,
    error::ParseError,
    interpreter::{
        lexer::Token,
        parser::{binary::parse_logical_or, unary::parse_do_block},
    },
};

pub type ParseResult<T> = Result<T, ParseError>;

/// Parses a full expression.
///
/// This is the entry point for expression parsing.
/// It begins at the lowest-precedence level, logical OR, and recursively
/// descends through the precedence hierarchy.
///
/// Grammar: `expression := logical_or`
///
/// # Parameters
/// - `tokens`: Token iterator providing `(Token, line)` pairs.
///
/// # Returns
/// The parsed expression node.
pub fn parse_expression<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    parse_logical_or(tokens)
}
/// Parses an `if` expression with optional `else` and chained `else if`.
///
/// Syntax:
/// ```text
///     if <condition> do <then_expr>
///     else if <condition> do <expr>
///     else do <expr>
/// ```
/// The `do` keyword begins the body expression for each branch.
/// Nested `else if` constructs are parsed recursively.
///
/// # Parameters
/// - `tokens`: Token stream positioned after the `if` keyword.
/// - `line`: Line number of the `if` token.
///
/// # Returns
/// An `Expr::IfExpr` node representing the full conditional expression.
///
/// # Errors
/// - `UnexpectedToken` if the expected `do`, `if`, or `else` keywords are
///   missing.
/// - Propagates any errors from sub-expression parsing.
pub fn parse_if<'a, I>(tokens: &mut Peekable<I>, line: usize) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let condition = parse_expression(tokens)?;

    match tokens.peek() {
        Some((Token::Do, _)) => {},
        _ => {
            return Err(ParseError::UnexpectedToken {
                token: "Expected 'do' after if condition".to_string(),
                line,
            });
        },
    }

    let then_expr = parse_do_block(tokens)?;

    let else_branch = match tokens.peek() {
        Some((Token::Else, _)) => {
            tokens.next();

            match tokens.peek() {
                Some((Token::If, line2)) => {
                    tokens.next();
                    Some(Box::new(parse_if(tokens, *line2)?))
                },

                Some((Token::Do, _)) => Some(Box::new(parse_do_block(tokens)?)),

                _ => {
                    return Err(ParseError::UnexpectedToken {
                        token: "Expected 'if' or 'do' after else".to_string(),
                        line,
                    });
                },
            }
        },

        _ => None,
    };

    Ok(Expr::IfExpr { condition: Box::new(condition),
                      then_branch: Box::new(then_expr),
                      else_branch,
                      line })
}
