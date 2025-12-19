/// Built-in function implementations.
///
/// Contains core mathematical and utility functions available by default in the
/// interpreter.
pub mod builtin;
/// The `clamp` function implementation.
///
/// Restricts a value to a specified inclusive range.
pub mod clamp;
/// The `conj` (complex conjugate) function implementation.
///
/// Computes the complex conjugate of a number.
pub mod conj;
/// Logarithm function implementations.
///
/// Supports various logarithms, including natural and base-n.
pub mod log;
/// `min` and `max` function implementations.
///
/// Returns the minimum or maximum value from a list of arguments.
pub mod min_max;
/// The `print` function implementation.
///
/// Outputs a value to the standard output or REPL.
pub mod print;
/// The `sqrt` (square root) function implementation.
///
/// Computes the square root for real, integer, or complex values.
pub mod sqrt;
/// The `trunc` (truncate) function implementation.
///
/// Removes the fractional part of a real number, returning its integer part.
pub mod trunc;

pub mod core;

pub mod transpose;
