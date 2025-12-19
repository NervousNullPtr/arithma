use std::iter::Peekable;

use crate::{
    ast::Expr,
    interpreter::{
        lexer::Token,
        parser::{core::ParseResult, statement::parse_statement},
    },
};

/// Parses a block expression delimited by braces.
///
/// A block consists of zero or more statements, optionally separated by
/// newlines. Parsing continues until a closing `}` token is encountered.
/// Leading and trailing newlines inside the block are ignored.
///
/// Grammar: `block := "{" statement* "}"`
///
/// The resulting expression is returned as `Expr::Block { statements, line }`.
///
/// # Parameters
/// - `tokens`: Token stream positioned after the opening brace.
/// - `line`: Line number of the opening brace.
///
/// # Returns
/// A block expression containing all parsed statements.
pub fn parse_block<'a, I>(tokens: &mut Peekable<I>, line: usize) -> ParseResult<Expr>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let mut statements = Vec::new();

    while tokens.peek().is_some() {
        while let Some((Token::NewLine, _)) = tokens.peek() {
            tokens.next();
        }

        if let Some((Token::RBrace, _)) = tokens.peek() {
            tokens.next();
            break;
        }

        statements.push(parse_statement(tokens)?);

        while let Some((Token::NewLine, _)) = tokens.peek() {
            tokens.next();
        }
    }

    Ok(Expr::Block { statements, line })
}
