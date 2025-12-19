/// Numeric conversion helpers.
///
/// This module provides safe functions for converting between integer and
/// floating-point types without risking silent data loss or rounding errors.
/// Use these helpers whenever you need to convert between `i64`, `u64`,
/// `usize`, and `f64` in a way that guarantees correctness.
///
/// All functions return a `Result`, which is `Ok` if the conversion is lossless
/// and valid, or an error if the value is out of range or not an integer.
pub mod num;
