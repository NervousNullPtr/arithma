/// Binary operator evaluation logic.
///
/// Handles the execution of all binary operations in expressions, including
/// arithmetic, comparisons, logical operators, and set operations.
pub mod binary;

/// Unary operator evaluation logic.
///
/// Implements all unary operations, such as arithmetic negation, logical NOT,
/// and factorial.
pub mod unary;

/// Core evaluation logic and context management.
///
/// Contains the main evaluation engine, the runtime context, value promotion,
/// and error propagation.
pub mod core;

/// Evaluation of for-loop expressions.
///
/// Supports loop constructs, manages iteration variables, and executes the loop
/// body in context.
pub mod for_loop;

/// Utility functions for evaluation.
///
/// Provides helpers and reusable routines shared by evaluation logic.
pub mod utils;

/// Function evaluation.
///
/// Handles user-defined and built-in function calls, argument checking, and
/// return value computation.
pub mod function;
