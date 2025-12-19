/// Complex number support.
///
/// Defines the `ComplexNumber` type used for arithmetic with real and imaginary
/// parts. Includes implementations for basic arithmetic operations, absolute
/// value, and conversions between real, integer, and complex values.
///
/// Complex numbers are fully supported in expressions and can participate in
/// mixed-type math.
pub mod complex;
/// Set value representation.
///
/// Defines the `SetValue` type, which is used for the elements of a
/// `Value::Set`. Ensures that set elements are unique and supports nested sets
/// and arrays.
///
/// This module provides the necessary logic for set membership, comparison, and
/// set operations.
pub mod set_value;

pub mod core;
