use std::iter::Peekable;

use crate::{
    ast::{BinaryOperator, FunctionDef, Statement},
    error::ParseError,
    interpreter::{
        evaluator::utils::is_reserved_identifier,
        lexer::Token,
        parser::{
            core::{ParseResult, parse_expression},
            utils::{parse_comma_separated, parse_identifier},
        },
    },
    util::num::i64_to_f64_checked,
};

// Parses a single statement.
/// A statement may be one of:
/// - a tolerance attribute (`rel_tol = ...`, `abs_tol = ...`).
/// - a variable declaration.
/// - an assignment.
/// - a function definition.
/// - an expression used as a statement.
///
/// Parsing is attempted in that order; the first matching construct is
/// returned. If none match, the input is parsed as an expression statement.
///
/// The statement’s source line is taken from the next available token.
///
/// # Parameters
/// - `tokens`: Token iterator containing `(Token, line)` pairs.
///
/// # Returns
/// A parsed [`Statement`] node.
pub fn parse_statement<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Statement>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    if let Some(statement) = parse_tolerance_attr(tokens)? {
        return Ok(statement);
    }
    if let Some(statement) = parse_variable_declaration(tokens)? {
        return Ok(statement);
    }
    if let Some(statement) = parse_assignment(tokens)? {
        return Ok(statement);
    }
    if let Some(statement) = parse_function_definition(tokens)? {
        return Ok(statement);
    }

    let current_line = tokens.peek().map_or(0, |(_, l)| *l);
    let expr = parse_expression(tokens)?;

    Ok(Statement::Expression { expr,
                               line: current_line })
}

/// Parses a tolerance attribute in the form:
///
///     #[rel_tolerance(value)]
///     #[abs_tolerance(value)]
///
/// Attributes begin with `#` followed by `[...]`.
/// Inside the brackets, the parser expects ` <identifier> "(" <numeric literal>
/// ")"`.
///
/// Valid identifiers:
/// - `rel_tolerance`
/// - `abs_tolerance`
///
/// If the attribute is valid, the corresponding `Statement::SetRelTolerance`
/// or `Statement::SetAbsTolerance` is returned.
/// If no attribute is present at the current position, returns `Ok(None)`.
///
/// # Errors
/// Returns a `ParseError` if:
/// - brackets or parentheses are missing,
/// - the attribute name is unknown,
/// - the value is not numeric,
/// - tokens run out unexpectedly.
///
/// # Parameters
/// - `tokens`: Token stream beginning at a possible `#` token.
///
/// # Returns
/// - `Ok(Some(statement))` if an attribute was parsed,
/// - `Ok(None)` if no attribute is present.
fn parse_tolerance_attr<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Option<Statement>>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    if let Some((Token::Hash, _)) = tokens.peek() {
        tokens.next();

        match tokens.next() {
            Some((Token::LBracket, line)) => {
                let attr_name = match tokens.next() {
                    Some((Token::Identifier(name), _)) => name.as_str(),
                    Some((tok, line)) => {
                        return Err(ParseError::UnexpectedToken { token: format!("Expected attribute name, found {tok:?}"),
                                                                 line:  *line, });
                    },
                    None => return Err(ParseError::UnexpectedEndOfInput { line: *line }),
                };
                // Expect '('
                match tokens.next() {
                    Some((Token::LParen, _)) => {},
                    _ => {
                        return Err(ParseError::UnexpectedToken {
                            token: "Expected '(' after attribute name.".to_string(),
                            line: *line,
                        });
                    },
                }
                // Parse value
                let value = match tokens.next() {
                    Some((Token::Real(val), _)) => *val,
                    Some((Token::Integer(val), _)) => {
                        i64_to_f64_checked(*val, ParseError::LiteralTooLarge { line: *line })?
                    },
                    Some((tok, line)) => {
                        return Err(ParseError::UnexpectedToken { token: format!("Expected numeric value, found {tok:?}"),
                                                                 line:  *line, });
                    },
                    None => return Err(ParseError::UnexpectedEndOfInput { line: *line }),
                };
                // Expect ')'
                match tokens.next() {
                    Some((Token::RParen, _)) => {},
                    _ => {
                        return Err(ParseError::UnexpectedToken {
                            token: "Expected ')' after attribute value.".to_string(),
                            line: *line,
                        });
                    },
                }
                // Expect ']'
                match tokens.next() {
                    Some((Token::RBracket, _)) => {},
                    _ => {
                        return Err(ParseError::UnexpectedToken {
                            token: "Expected ']' after attribute.".to_string(),
                            line: *line,
                        });
                    },
                }

                match attr_name {
                    "rel_tolerance" => return Ok(Some(Statement::SetRelTolerance(value))),
                    "abs_tolerance" => return Ok(Some(Statement::SetAbsTolerance(value))),
                    _ => {
                        return Err(ParseError::UnexpectedToken { token: format!("Unknown attribute #[{attr_name}]"),
                                                                 line:  *line, });
                    },
                }
            },
            _ => {
                return Err(ParseError::UnexpectedToken { token:
                                                             "Expected '[' after '#'".to_string(),
                                                         line:  0, });
            },
        }
    }

    Ok(None)
}

/// Parses a variable declaration statement.
///
/// A declaration has the form `let <identifier> = <expression>`.
///
/// The identifier must not be a reserved name.
/// After the `=` token, a full expression is parsed as the initializer.
///
/// If the next token is not `let`, this function returns `Ok(None)` and does
/// not consume any input.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at a possible `let`.
///
/// # Returns
/// - `Ok(Some(Statement::VariableDeclaration))` if a declaration is parsed,
/// - `Ok(None)` if no declaration is present.
///
/// # Errors
/// Returns a `ParseError` if:
/// - the identifier is reserved,
/// - `=` is missing,
/// - the expression is malformed,
/// - input ends unexpectedly.
fn parse_variable_declaration<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Option<Statement>>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    if let Some((Token::Let, line)) = tokens.peek() {
        let line = *line;
        tokens.next();

        let name = parse_identifier(tokens)?;
        if is_reserved_identifier(&name) {
            return Err(ParseError::IdentifierReserved { name, line });
        }

        match tokens.next() {
            Some((Token::Equals, _)) => {},
            Some((tok, l)) => {
                return Err(ParseError::UnexpectedToken { token: format!("Expected '=', found {tok:?}"),
                                                         line:  *l, });
            },
            None => {
                return Err(ParseError::UnexpectedEndOfInput { line });
            },
        }

        let value = parse_expression(tokens)?;
        return Ok(Some(Statement::VariableDeclaration { name, value, line }));
    }

    Ok(None)
}

/// Parses an assignment or compound-assignment statement.
///
/// Supported forms:
///
/// - `<identifier> = <expression>`
/// - `<identifier> += <expression>`
/// - `<identifier> -= <expression>`
/// - `<identifier> *= <expression>`
/// - `<identifier> /= <expression>`
///
/// The function performs a limited lookahead:
/// if the next token is an identifier and the following token is `=` or one of
/// the compound-assignment operators, an assignment is parsed.
///
/// Reserved identifiers cannot be assigned to.
///
/// If no assignment pattern matches, the function returns `Ok(None)` and does
/// not consume tokens.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at a potential identifier.
///
/// # Returns
/// - `Ok(Some(Statement::Assignment))` for simple assignments,
/// - `Ok(Some(Statement::CompoundAssignment))` for compound operators,
/// - `Ok(None)` if no assignment is present.
///
/// # Errors
/// Returns a `ParseError` if:
/// - the identifier is reserved,
/// - the assignment operator is followed by invalid syntax,
/// - the assigned expression fails to parse.
fn parse_assignment<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Option<Statement>>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    if let Some((Token::Identifier(_), _)) = tokens.peek() {
        let mut lookahead = tokens.clone();
        lookahead.next();
        match lookahead.peek() {
            Some((Token::Equals, line)) => {
                let name = if let Some((Token::Identifier(n), _)) = tokens.next() {
                    n.clone()
                } else {
                    unreachable!()
                };

                if is_reserved_identifier(&name) {
                    return Err(ParseError::IdentifierReserved { name, line: *line });
                }
                tokens.next();

                let value = parse_expression(tokens)?;
                return Ok(Some(Statement::Assignment { name,
                                                       value,
                                                       line: *line }));
            },
            Some((Token::PlusAssign
                  | Token::MinusAssign
                  | Token::MulAssign
                  | Token::DivAssign,
                  line)) => {
                let name = if let Some((Token::Identifier(n), _)) = tokens.next() {
                    n.clone()
                } else {
                    unreachable!()
                };
                let (op_token, _) = tokens.next().unwrap();
                let value = parse_expression(tokens)?;
                let op = match op_token {
                    Token::PlusAssign => BinaryOperator::Add,
                    Token::MinusAssign => BinaryOperator::Sub,
                    Token::MulAssign => BinaryOperator::Mul,
                    Token::DivAssign => BinaryOperator::Div,
                    _ => unreachable!(),
                };
                return Ok(Some(Statement::CompoundAssignment { name,
                                                               op,
                                                               value,
                                                               line: *line }));
            },
            _ => {},
        }
    }
    Ok(None)
}

/// Parses a function definition of the form `<name>(param1, param2, ...) =
/// <expression>`.
///
/// This function identifies a definition by checking:
/// 1. The next token is an identifier.
/// 2. It is immediately followed by `(`.
/// 3. A matching `)` exists (nested parentheses inside parameters are allowed).
/// 4. The token after the closing `)` is `=`.
///
/// When these conditions are met, the function name, parameter list, and body
/// expression are parsed and returned as a `Statement::Function`.
///
/// If the input does not match a function definition, the function returns
/// `Ok(None)` without consuming tokens.
///
/// # Parameters
/// - `tokens`: Token iterator positioned at a potential function name.
///
/// # Returns
/// - `Ok(Some(Statement::Function))` if a definition is parsed,
/// - `Ok(None)` if no definition is present.
///
/// # Errors
/// Returns a `ParseError` if:
/// - parentheses do not balance,
/// - parameters fail to parse,
/// - the `=` is missing,
/// - the body expression fails to parse,
/// - input ends unexpectedly.
fn parse_function_definition<'a, I>(tokens: &mut Peekable<I>) -> ParseResult<Option<Statement>>
    where I: Iterator<Item = &'a (Token, usize)> + Clone
{
    let current_line = tokens.peek().map_or(0, |(_, l)| *l);
    if let Some((Token::Identifier(_), _)) = tokens.peek() {
        let mut lookahead = tokens.clone();
        lookahead.next();

        if let Some((Token::LParen, _)) = lookahead.peek() {
            let mut lookahead = lookahead.clone();
            lookahead.next();
            let mut parens = 1;

            while parens > 0 {
                match lookahead.next() {
                    Some((Token::LParen, _)) => parens += 1,
                    Some((Token::RParen, _)) => parens -= 1,
                    Some(_) => {},
                    None => return Err(ParseError::UnexpectedEndOfInput { line: current_line }),
                }
            }

            if let Some((Token::Equals, line)) = lookahead.peek() {
                let name = if let Some((Token::Identifier(n), _)) = tokens.next() {
                    n.clone()
                } else {
                    unreachable!()
                };
                tokens.next();

                let params = parse_comma_separated(tokens, parse_identifier, &Token::RParen)?;
                tokens.next();

                let body = parse_expression(tokens)?;
                return Ok(Some(Statement::Function(FunctionDef { name,
                                                                 params,
                                                                 body,
                                                                 line: *line })));
            }
        }
    }
    Ok(None)
}
