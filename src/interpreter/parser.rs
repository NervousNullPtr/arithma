/// Core evaluation logic for expressions and values.
///
/// Contains shared evaluation routines, context handling, and core error
/// propagation.
pub mod core;

/// Unary operator evaluation.
///
/// Handles all operations that take a single operand, such as negation and
/// factorial.
pub mod unary;

/// Binary operator evaluation.
///
/// Implements evaluation for all binary operations, including arithmetic,
/// comparisons, and logical operators.
pub mod binary;

/// Block evaluation.
///
/// Evaluates sequences of statements grouped in blocks, managing scoping and
/// local context.
pub mod block;

/// Utility functions for the evaluator.
///
/// Provides helpers, common checks, and reusable logic used during expression
/// evaluation.
pub mod utils;

/// Statement evaluation.
///
/// Implements logic for evaluating top-level statements, including assignments,
/// declarations, and directives.
pub mod statement;
