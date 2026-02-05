use std::{collections::HashSet, rc::Rc};

use ordered_float::OrderedFloat;

use crate::{
    ast::LiteralValue,
    error::RuntimeError,
    interpreter::{
        evaluator::core::EvalResult,
        value::{complex::ComplexNumber, set_value::SetValue},
    },
    util::num::{f64_to_i64_checked, i64_to_f64_checked},
};

/// Represents a runtime value in the interpreter.
///
/// This enum models all the possible types that can appear in expressions,
/// assignments, function returns, and conditional evaluations.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A numeric value (double precision floating-point).
    Real(f64),
    /// A integer value (64 bit integer).
    Integer(i64),
    /// A boolean value (`true` or `false`).
    /// Produced by comparison operators (`<`, `==`, `!=`, etc.) or logical
    /// operations (`!`). Used primarily as conditions in `if` expressions,
    /// where the condition must evaluate to `Bool`.
    Bool(bool),
    /// An array of `Value` elements.
    Array(Rc<Vec<Self>>),
    /// A complex number (with real and imaginary parts).
    Complex(ComplexNumber),
    /// A set of unique values.
    Set(Rc<HashSet<SetValue>>),
}

impl From<ComplexNumber> for Value {
    fn from(c: ComplexNumber) -> Self {
        Self::Complex(c)
    }
}

impl From<f64> for Value {
    fn from(v: f64) -> Self {
        Self::Real(v)
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Self::Integer(v)
    }
}

impl From<bool> for Value {
    fn from(v: bool) -> Self {
        Self::Bool(v)
    }
}

impl From<Vec<Self>> for Value {
    fn from(v: Vec<Self>) -> Self {
        Self::Array(Rc::new(v))
    }
}

impl Value {
    /// Converts the value to an `f64`, or returns an error if not numeric.
    ///
    /// Accepts `Value::Real` and `Value::Integer`.
    /// For integers, conversion fails if the value is too large to be
    /// represented as `f64` exactly.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(f64)`: If value is real or a safe integer.
    /// - `Err(RuntimeError::ExpectedNumber | LiteralTooLarge)`: If not numeric
    ///   or not representable.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::core::Value;
    ///
    /// let x = Value::Integer(10);
    /// let real = x.as_real(42).unwrap();
    ///
    /// assert_eq!(real, 10.0);
    /// ```
    pub fn as_real(&self, line: usize) -> EvalResult<f64> {
        match self {
            Self::Real(r) => Ok(*r),
            Self::Integer(n) => Ok(i64_to_f64_checked(*n, RuntimeError::LiteralTooLarge { line })?),
            _ => Err(RuntimeError::ExpectedNumber { line }),
        }
    }
    /// Converts the value to `ComplexNumber`, or returns an error if not
    /// numeric.
    ///
    /// Accepts `Value::Complex`, `Value::Real`, and `Value::Integer`.
    /// Fails if value is not numeric or if integer is too large to be
    /// represented as `f64`.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(ComplexNumber)`: The converted complex value.
    /// - `Err(RuntimeError)`: If not numeric or out of range.
    pub fn as_complex(&self, line: usize) -> EvalResult<ComplexNumber> {
        match self {
            Self::Complex(c) => Ok(*c),
            Self::Real(r) => Ok(ComplexNumber::from(*r)),
            Self::Integer(n) => {
                Ok(ComplexNumber::from(i64_to_f64_checked(*n,
                                                          RuntimeError::LiteralTooLarge { line })?))
            },
            _ => Err(RuntimeError::ExpectedNumber { line }),
        }
    }
    /// Converts the value to `i64`, or returns an error if not an integer.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(i64)`: The integer value.
    /// - `Err(RuntimeError::ExpectedNumber)`: If not an integer.
    pub const fn as_integer(&self, line: usize) -> EvalResult<i64> {
        match self {
            Self::Integer(n) => Ok(*n),
            _ => Err(RuntimeError::ExpectedNumber { line }),
        }
    }
    /// Converts the value to `bool`, or returns an error if not boolean.
    ///
    /// Used for conditions in `if` expressions and logical operations.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(bool)`: The boolean value.
    /// - `Err(RuntimeError::ExpectedBoolean)`: If not boolean.
    pub const fn as_bool(&self, line: usize) -> EvalResult<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err(RuntimeError::ExpectedBoolean { line }),
        }
    }

    /// Converts the value to a vector of values, or returns an error if not an
    /// array.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(Vec<Value>)`: If the value is an array.
    /// - `Err(RuntimeError::ExpectedArray)`: If not an array.
    pub fn as_vec(&self, line: usize) -> EvalResult<&Vec<Self>> {
        match self {
            Self::Array(v) => Ok(v),
            _ => Err(RuntimeError::ExpectedArray { line }),
        }
    }
    /// Promotes an integer to a real value for mixed math, or returns values
    /// as-is if already matching.
    ///
    /// - If one side is an integer and the other is a real, the integer is
    ///   converted to a real.
    /// - Otherwise, both values are returned unchanged.
    ///
    /// # Parameters
    /// - `other`: The value to promote with.
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok((Self, Self))`: Promoted values.
    /// - `Err(RuntimeError)`: If conversion fails.
    pub fn promote_to_real(self, other: &Self, line: usize) -> EvalResult<(Self, Self)> {
        use Value::{Array, Integer, Real};

        match (&self, other) {
            (Real(_), Integer(_)) => Ok((self, Self::Real(other.as_real(line)?))),
            (Integer(_), Real(_)) => Ok((Real(self.as_real(line)?), other.clone())),
            (Array(arr), Real(_)) | (Real(_), Array(arr)) => {
                let promoted =
                    arr.iter()
                       .map(|value| value.clone().promote_to_real(other, line).map(|(x, _)| x))
                       .collect::<Result<Vec<_>, _>>()?;
                Ok((Array(promoted.into()), other.clone()))
            },
            _ => Ok((self, other.clone())),
        }
    }
    /// Promotes any number to complex for mixed math, or returns values as-is
    /// if already matching.
    ///
    /// # Parameters
    /// - `other`: The value to promote with.
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok((Self, Self))`: Promoted values.
    /// - `Err(RuntimeError)`: If conversion fails.
    pub fn promote_to_complex(self, other: &Self, line: usize) -> EvalResult<(Self, Self)> {
        use Value::{Array, Complex};

        match (&self, other) {
            (Array(arr), Complex(_)) | (Complex(_), Array(arr)) => {
                let mut promoted = Vec::with_capacity(arr.len());
                for val in arr.iter() {
                    promoted.push(Self::Complex(val.clone().as_complex(line)?));
                }
                Ok((Array(promoted.into()), other.clone()))
            },
            (Complex(_), _) => {
                let right = Self::Complex(other.as_complex(line)?);
                Ok((self, right))
            },
            (_, Complex(_)) => {
                let left = Self::Complex(self.as_complex(line)?);
                Ok((left, other.clone()))
            },

            _ => Ok((self, other.clone())),
        }
    }
    /// Returns the absolute value of a numeric value.
    ///
    /// # Panics
    /// Panics if called on a non-numeric or complex value.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(Value)`: The absolute value.
    /// - `Err(RuntimeError::ExpectedNumber)`: If value is not numeric.
    pub fn abs(&self, line: usize) -> EvalResult<Self> {
        match self {
            Self::Complex(c) => Ok(c.abs().into()),
            Self::Integer(i) => Ok(i.abs().into()),
            _ => Ok(Self::Real(self.as_real(line)?.abs())),
        }
    }
    /// Returns the signumof a numeric value.
    ///
    /// # Panics
    /// Panics if called on a non-numeric value.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(Value)`: The absolute value.
    /// - `Err(RuntimeError::ExpectedNumber)`: If value is not numeric.
    pub fn sign(&self, line: usize) -> EvalResult<Self> {
        match self {
            Self::Integer(i) => Ok(i.signum().into()),
            Self::Real(r) => Ok(r.signum().into()),
            _ => Ok(Self::Real(self.as_real(line)?.abs())),
        }
    }
    /// Converts the value to `f64` if numeric, otherwise returns an error.
    ///
    /// This is equivalent to `as_real` for compatibility.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(f64)`: The numeric value as `f64`.
    /// - `Err(RuntimeError::ExpectedNumber | LiteralTooLarge)`: If not numeric
    ///   or not representable.
    pub fn as_numeric_f64(&self, line: usize) -> EvalResult<f64> {
        match self {
            Self::Real(n) => Ok(*n),
            Self::Integer(i) => Ok(i64_to_f64_checked(*i, RuntimeError::LiteralTooLarge { line })?),
            _ => Err(RuntimeError::ExpectedNumber { line }),
        }
    }
    /// Converts a [`Value`] to an `i64`, performing safe conversion if
    /// necessary.
    ///
    /// - Accepts `Value::Integer` directly.
    /// - Converts `Value::Real` to `i64` if the value is finite, within the
    ///   `i64` range, and not fractional.
    /// - Returns an error if the value is not numeric or if conversion would
    ///   lose precision.
    ///
    /// # Parameters
    /// - `line`: Source code line number for error reporting.
    ///
    /// # Returns
    /// - `Ok(i64)`: The integer value if conversion succeeds.
    /// - `Err(RuntimeError)`: If the value is not numeric or cannot be safely
    ///   converted.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::core::Value;
    ///
    /// let int_val = Value::Integer(42);
    /// assert_eq!(int_val.value_to_i64(1).unwrap(), 42);
    ///
    /// let real_val = Value::Real(10.0);
    /// assert_eq!(real_val.value_to_i64(1).unwrap(), 10);
    ///
    /// let non_int_val = Value::Real(1.23);
    /// assert!(non_int_val.value_to_i64(1).is_err());
    /// ```
    pub fn value_to_i64(&self, line: usize) -> EvalResult<i64> {
        match self {
            Self::Integer(i) => Ok(*i),
            Self::Real(r) => Ok(f64_to_i64_checked(*r, line)?),
            _ => Err(RuntimeError::ExpectedNumber { line }),
        }
    }
    /// Returns `true` if the value is [`Real`].
    #[allow(dead_code)]
    #[must_use]
    pub const fn is_real(&self) -> bool {
        matches!(self, Self::Real(..))
    }

    /// Returns `true` if the value is [`Integer`].
    #[must_use]
    pub const fn is_integer(&self) -> bool {
        matches!(self, Self::Integer(..))
    }

    /// Returns `true` if the value is [`Array`].
    #[must_use]
    pub const fn is_array(&self) -> bool {
        matches!(self, Self::Array(..))
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Real(r) => write!(f, "{r}"),
            Self::Integer(n) => write!(f, "{n}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Array(a) => {
                write!(f, "[")?;

                for (index, value) in a.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{value}")?;
                }

                write!(f, "]")
            },
            Self::Complex(c) => write!(f, "{c}"),
            Self::Set(s) => {
                fn print_key(
                    val: &SetValue)
                    -> (u8, Option<i128>, Option<OrderedFloat<f64>>, Option<bool>, String)
                {
                    match val {
                        SetValue::Bool(b) => (0, None, None, Some(*b), String::new()),
                        SetValue::Integer(n) => {
                            (1, Some(i128::from(*n)), None, None, String::new())
                        },
                        SetValue::Real(r) => (2, None, Some(*r), None, String::new()),
                        SetValue::Complex(_) => (3, None, None, None, format!("{val}")),
                        SetValue::Array(_) => (4, None, None, None, format!("{val}")),
                        SetValue::Set(_) => (5, None, None, None, format!("{val}")),
                    }
                }

                let mut elems: Vec<&SetValue> = s.iter().collect();
                elems.sort_by(|a, b| {
                         let ka = print_key(a);
                         let kb = print_key(b);
                         ka.cmp(&kb)
                     });

                write!(f, "{{")?;
                for (i, v) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "}}")
            },
        }
    }
}

impl From<&LiteralValue> for Value {
    fn from(lit: &LiteralValue) -> Self {
        match lit {
            LiteralValue::Real(n) => (*n).into(),
            LiteralValue::Integer(i) => (*i).into(),
            LiteralValue::Bool(b) => (*b).into(),
            LiteralValue::Complex(complex) => (*complex).into(),
        }
    }
}
