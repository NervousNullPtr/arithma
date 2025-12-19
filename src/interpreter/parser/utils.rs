use std::iter::Peekable;

use crate::{
    ast::Expr,
    error::ParseError,
    interpreter::{
        lexer::Token,
        parser::core::{ParseResult, parse_expression},
    },
};

/// Parses a comma-separated list of items until a closing token.
///
/// This utility is shared by array literals, function argument lists,
/// and set literals. It repeatedly calls `parse_item` to parse one element,
/// expecting either:
///
/// - a comma, to continue the list, or
/// - the specified closing token, to end it.
///
/// An immediately encountered closing token produces an empty list.
///
/// Grammar (simplified): `list := item ("," item)*`
///
/// # Parameters
/// - `tokens`: Token iterator positioned at the first item or closing token.
/// - `parse_item`: Function used to parse each list element.
/// - `closing`: The token that terminates the list (e.g., `]` or `)`).
///
/// # Returns
/// A vector of parsed items.
///
/// # Errors
/// Returns a `ParseError` if:
/// - an item fails to parse,
/// - an unexpected token is encountered,
/// - the stream ends before the closing token.
pub(in crate::interpreter::parser) fn parse_comma_separated<'a, I, T>(
    tokens: &mut Peekable<I>,
    parse_item: impl Fn(&mut Peekable<I>) -> ParseResult<T>,
    closing: &Token)
    -> Result<Vec<T>, ParseError>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut items = Vec::new();
    if let Some((tok, _)) = tokens.peek()
       && tok == closing
    {
        tokens.next();

        return Ok(items);
    }
    loop {
        items.push(parse_item(tokens)?);
        match tokens.peek() {
            Some((Token::Comma, _)) => {
                tokens.next();
            },
            Some((tok, _)) if tok == closing => {
                tokens.next();
                break;
            },
            Some((tok, line)) => {
                return Err(ParseError::UnexpectedToken { token: format!("Expected ',' or {closing:?}, found {tok:?}"),
                                                         line:  *line, });
            },
            None => return Err(ParseError::UnexpectedEndOfInput { line: 0 }),
        }
    }
    Ok(items)
}

/// Parses a plain identifier and returns its name.
///
/// The next token must be `Token::Identifier`.
/// This function does not check for reserved identifiers; callers must handle
/// that.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at an identifier.
///
/// # Returns
/// A `String` containing the identifier.
///
/// # Errors
/// Returns a `ParseError` if:
/// - the next token is not an identifier,
/// - the input ends unexpectedly.
pub(in crate::interpreter::parser) fn parse_identifier<'a, I>(tokens: &mut Peekable<I>)
                                                              -> ParseResult<String>
    where I: Iterator<Item = &'a (Token, usize)>
{
    match tokens.next() {
        Some((Token::Identifier(s), _)) => Ok(s.clone()),
        Some((tok, line)) => {
            Err(ParseError::UnexpectedToken { token: format!("Expected identifier, found {tok:?}"),
                                              line:  *line, })
        },
        None => Err(ParseError::UnexpectedEndOfInput { line: 0 }),
    }
}

/// Parses a set literal of the form `{ expr1, expr2, ..., exprN }`.
///
/// Elements are parsed using [`parse_expression`] and collected into an
/// `Expr::SetLiteral` node.
/// An empty set `{}` is accepted.
///
/// Grammar: `set := "{" (expression ("," expression)*)? "}"`.
/// # Parameters
/// - `tokens`: Token iterator positioned at `{`.
///
/// # Returns
/// An `Expr::SetLiteral` with its list of element expressions.
///
/// # Errors
/// Returns a `ParseError` if:
/// - `{` is missing,
/// - elements fail to parse,
/// - the closing `}` is missing.
pub fn parse_set_literal<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let (_, line) = match tokens.next() {
        Some((Token::LBrace, line)) => (Token::LBrace, line),
        Some((tok, line)) => {
            return Err(ParseError::UnexpectedToken { token: format!("expected '{{', found {tok:?}"),
                                                     line:  *line, });
        },
        None => return Err(ParseError::UnexpectedEndOfInput { line: 0 }),
    };

    let elements = parse_comma_separated(tokens, parse_expression, &Token::RBrace)?;

    Ok(Expr::SetLiteral { elements,
                          line: *line })
}
