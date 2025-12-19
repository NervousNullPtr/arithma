use crate::{error::RuntimeError, interpreter::evaluator::core::EvalResult};

/// Largest integer value exactly representable as an `f64` (`2^53 - 1`).
pub const MAX_SAFE_U64_INT: u64 = 9_007_199_254_740_991;
/// Largest signed integer exactly representable as an `f64` (`2^53 - 1`).
pub const MAX_SAFE_I64_INT: i64 = 9_007_199_254_740_991;

/// Safely converts an `i64` to `f64` if and only if it is exactly
/// representable.
///
/// ## Errors
/// Returns `Err(error)` if the value exceeds `MAX_SAFE_U64_INT` in absolute
/// value.
///
/// ## Parameters
/// - `value`: The integer to convert.
/// - `error`: The error to return if conversion is not lossless.
///
/// ## Returns
/// - `Ok(f64)`: The converted value if it is safe.
/// - `Err(error)`: If the value is too large.
///
/// ## Example
/// ```
/// use arithma::util::num::{MAX_SAFE_U64_INT, i64_to_f64_checked};
///
/// // Works for safe values
/// let result = i64_to_f64_checked(42, "too big!");
/// assert_eq!(result.unwrap(), 42.0);
///
/// // Fails for values outside safe range
/// let big = MAX_SAFE_U64_INT as i64 + 1;
/// assert!(i64_to_f64_checked(big, "too big!").is_err());
/// ```
#[allow(clippy::cast_precision_loss)]
pub fn i64_to_f64_checked<E>(value: i64, error: E) -> Result<f64, E> {
    if value.unsigned_abs() > MAX_SAFE_U64_INT {
        return Err(error);
    }
    Ok(value as f64)
}
/// Safely converts a `u64` to `f64` if and only if it is exactly representable.
///
/// ## Errors
/// Returns an error if the value exceeds `MAX_SAFE_U64_INT`.
///
/// ## Parameters
/// - `value`: The unsigned integer to convert.
/// - `line`: Source code line number for error reporting.
///
/// ## Returns
/// - `Ok(f64)`: The converted value if safe.
/// - `Err(RuntimeError::LiteralTooLarge { line })`: If the value is too large.
///
/// ## Example
/// ```
/// use arithma::{
///     error::RuntimeError,
///     util::num::{MAX_SAFE_U64_INT, u64_to_f64_checked},
/// };
///
/// // Safe value
/// let val = u64_to_f64_checked(1234, 0).unwrap();
/// assert_eq!(val, 1234.0);
///
/// // Unsafe value
/// let too_big = MAX_SAFE_U64_INT + 1;
/// let err = u64_to_f64_checked(too_big, 42).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 42 }));
/// ```
#[allow(clippy::cast_precision_loss)]
pub const fn u64_to_f64_checked(value: u64, line: usize) -> EvalResult<f64> {
    if value > MAX_SAFE_U64_INT {
        return Err(RuntimeError::LiteralTooLarge { line });
    }

    Ok(value as f64)
}
/// Safely converts a `usize` to `f64` if and only if it is exactly
/// representable. ## Errors
/// Returns an error if the value exceeds `MAX_SAFE_U64_INT`.
///
/// # Parameters
/// - `value`: The value to convert.
/// - `line`: Source code line number for error reporting.
///
/// # Returns
/// - `Ok(f64)`: The converted value if safe.
/// - `Err(RuntimeError::LiteralTooLarge { line })`: If the value is too large.
///
/// # Example
/// ```
/// use arithma::{
///     error::RuntimeError,
///     util::num::{MAX_SAFE_U64_INT, usize_to_f64_checked},
/// };
///
/// // Safe conversion
/// let val = usize_to_f64_checked(100, 0).unwrap();
/// assert_eq!(val, 100.0);
///
/// // Unsafe conversion
/// let too_big = (MAX_SAFE_U64_INT + 1) as usize;
/// let err = usize_to_f64_checked(too_big, 77).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 77 }));
/// ```
pub const fn usize_to_f64_checked(value: usize, line: usize) -> EvalResult<f64> {
    u64_to_f64_checked(value as u64, line)
}
/// Safely converts an `f64` to `i64` if the value is finite, within range, and
/// not fractional. ## Errors
/// Returns an error for non-finite, out-of-range, or fractional values.
///
/// # Parameters
/// - `value`: The floating-point value to convert.
/// - `line`: Source code line number for error reporting.
///
/// # Returns
/// - `Ok(i64)`: The converted value if safe.
/// - `Err(RuntimeError::TypeError | LiteralTooLarge | RealIsFractional)`: If
///   conversion is invalid.
///
/// # Example
/// ```
/// use arithma::{error::RuntimeError, util::num::f64_to_i64_checked};
///
/// // Safe conversion
/// let x = 1000.0;
/// let int = f64_to_i64_checked(x, 1).unwrap();
/// assert_eq!(int, 1000);
///
/// // Fractional value
/// let err = f64_to_i64_checked(1.5, 123).unwrap_err();
/// assert!(matches!(err, RuntimeError::RealIsFractional { line: 123 }));
///
/// // Out of range
/// let big = 1e20;
/// let err = f64_to_i64_checked(big, 5).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 5 }));
/// ```
#[allow(clippy::cast_possible_truncation)]
#[allow(clippy::cast_precision_loss)]
pub fn f64_to_i64_checked(value: f64, line: usize) -> EvalResult<i64> {
    if !value.is_finite() {
        return Err(RuntimeError::TypeError { details: format!("Cannot convert non-finite value {value} to i64"),
                                             line });
    }
    // Check range (inclusive, using truncation)
    if value < i64::MIN as f64 || value > i64::MAX as f64 {
        return Err(RuntimeError::LiteralTooLarge { line });
    }
    // Check for integral value
    if value.fract() != 0.0 {
        return Err(RuntimeError::RealIsFractional { line });
    }
    Ok(value as i64)
}
/// Safely converts an `f64` to `u64` if the value is finite, non-negative,
/// within range, and not fractional. ## Errors
/// Returns an error for non-finite, negative, out-of-range, or fractional
/// values.
///
/// # Parameters
/// - `value`: The floating-point value to convert.
/// - `line`: Source code line number for error reporting.
///
/// # Returns
/// - `Ok(u64)`: The converted value if safe.
/// - `Err(RuntimeError::TypeError | LiteralTooLarge | RealIsFractional)`: If
///   conversion is invalid.
///
/// # Example
/// ```
/// use arithma::{error::RuntimeError, util::num::f64_to_u64_checked};
///
/// // Safe
/// let u = f64_to_u64_checked(7.0, 9).unwrap();
/// assert_eq!(u, 7);
///
/// // Negative value
/// let err = f64_to_u64_checked(-5.0, 10).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 10 }));
///
/// // Fractional value
/// let err = f64_to_u64_checked(1.23, 11).unwrap_err();
/// assert!(matches!(err, RuntimeError::RealIsFractional { line: 11 }));
/// ```
#[allow(clippy::cast_possible_truncation)]
#[allow(clippy::cast_precision_loss)]
#[allow(clippy::cast_sign_loss)]
pub fn f64_to_u64_checked(value: f64, line: usize) -> EvalResult<u64> {
    if !value.is_finite() {
        return Err(RuntimeError::TypeError { details: format!("Cannot convert non-finite value {value} to i64"),
                                             line });
    }
    if value < 0.0 || value > MAX_SAFE_U64_INT as f64 {
        return Err(RuntimeError::LiteralTooLarge { line });
    }
    if value.fract() != 0.0 {
        return Err(RuntimeError::RealIsFractional { line });
    }
    Ok(value as u64)
}
/// Safely converts an `i64` to `u32` if and only if it is exactly
/// representable.
///
/// ## Errors
/// Returns `Err(error)` if the value exceeds `MAX_SAFE_U64_INT` in absolute
/// value.
///
/// # Parameters
/// - `value`: The floating-point value to convert.
/// - `line`: Source code line number for error reporting.
///
/// # Returns
/// - `Ok(i64)`: The converted value if safe.
/// - `Err(RuntimeError:: LiteralTooLarge | LiteralTooSmall)`: If conversion is
///   invalid.
///
/// # Example
/// ```
/// use arithma::{error::RuntimeError, util::num::i64_to_u32_checked};
///
/// // Safe
/// let u = i64_to_u32_checked(45, 5).unwrap();
/// assert_eq!(u, 45);
///
/// // Negative value
/// let err = i64_to_u32_checked(-1, 5).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooSmall { line: 5 }));
///
/// // Fractional value
/// let err = i64_to_u32_checked(i64::MAX, 11).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 11 }));
/// ```
#[allow(clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)]
pub const fn i64_to_u32_checked(value: i64, line: usize) -> EvalResult<u32> {
    if value > u32::MAX as i64 {
        return Err(RuntimeError::LiteralTooLarge { line });
    }

    if value < 0 {
        return Err(RuntimeError::LiteralTooSmall { line });
    }
    Ok(value as u32)
}
/// Safely converts an `i64` to a `usize` if and only if it can be represented
/// exactly.
///
/// ## Errors
/// Returns an error if the value is negative or exceeds the maximum
/// representable `usize`.
///
/// ## Parameters
/// - `value`: The integer value to convert.
/// - `line`: Source code line number for error reporting.
///
/// ## Returns
/// - `Ok(usize)`: The converted value if it is safe.
/// - `Err(RuntimeError::LiteralTooLarge | RuntimeError::LiteralTooSmall)`: If
///   conversion fails.
///
/// ## Example
/// ```
/// use arithma::{error::RuntimeError, util::num::i64_to_usize_checked};
///
/// // Safe
/// let v = i64_to_usize_checked(42, 0).unwrap();
/// assert_eq!(v, 42);
///
/// // Too small
/// let err = i64_to_usize_checked(-1, 5).unwrap_err();
/// assert!(matches!(err, RuntimeError::LiteralTooSmall { line: 5 }));
///
/// // Too large (only on 32-bit targets)
/// if cfg!(target_pointer_width = "32") {
///     let big = (u32::MAX as i64) + 1;
///     let err = i64_to_usize_checked(big, 7).unwrap_err();
///     assert!(matches!(err, RuntimeError::LiteralTooLarge { line: 7 }));
/// } else {
///     // On 64-bit systems, the same value is valid.
///     let big = (u32::MAX as i64) + 1;
///     let val = i64_to_usize_checked(big, 7).unwrap();
///     assert_eq!(val, big as usize);
/// }
/// !(matches!(err, RuntimeError::LiteralTooLarge { line: 7 }));
/// ```
pub fn i64_to_usize_checked(value: i64, line: usize) -> EvalResult<usize> {
    if value < 0 {
        return Err(RuntimeError::LiteralTooSmall { line });
    }

    usize::try_from(value).map_or(Err(RuntimeError::LiteralTooLarge { line }), Ok)
}
