use std::{
    cmp::Ordering,
    fmt::Display,
    hash::{Hash, Hasher},
    ops,
};

use ordered_float::OrderedFloat;

use crate::{
    error::RuntimeError,
    interpreter::{evaluator::core::EvalResult, value::core::Value},
};

/// `0.0` as a complex number.
pub const ZERO: ComplexNumber = ComplexNumber::new(0.0, 0.0);
/// `1.0` as a complex number.
pub const ONE: ComplexNumber = ComplexNumber::new(1.0, 0.0);

/// Represents a complex number with real and imaginary parts.
#[derive(Debug, Clone, Copy)]
pub struct ComplexNumber {
    /// The real part of the number.
    pub real:      f64,
    /// The imaginary part of the number.
    pub imaginary: f64,
}

impl Display for ComplexNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.real, self.imaginary) {
            (0.0, 0.0) => write!(f, "0"),
            (real, 0.0) => write!(f, "{real}"),
            (0.0, imaginary) => write!(f, "{imaginary}i",),
            (real, imaginary) if imaginary > 0.0 => write!(f, "{real} + {imaginary}i"),
            (real, imaginary) => write!(f, "{real} - {}i", -imaginary),
        }
    }
}

impl ComplexNumber {
    /// Constructs a new complex number from real and imaginary components.
    ///
    /// # Parameters
    /// - `real`: The real part.
    /// - `imaginary`: The imaginary part.
    ///
    /// # Returns
    /// The new `ComplexNumber`.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(5.0, -1.0);
    /// assert_eq!(c.real, 5.0);
    /// assert_eq!(c.imaginary, -1.0);
    /// ```
    #[must_use]
    pub const fn new(real: f64, imaginary: f64) -> Self {
        Self { real, imaginary }
    }

    /// Converts to a `Value::Real` if the imaginary part is zero, otherwise
    /// returns `Value::Complex`.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::{complex::ComplexNumber, core::Value};
    /// let real = ComplexNumber::new(3.0, 0.0);
    /// assert_eq!(real.checked_as_real(), Value::Real(3.0));
    ///
    /// let complex = ComplexNumber::new(2.0, 1.0);
    /// assert!(matches!(complex.checked_as_real(), Value::Complex(_)));
    /// ```
    #[must_use]
    pub const fn checked_as_real(&self) -> Value {
        if self.imaginary == 0.0 {
            Value::Real(self.real)
        } else {
            Value::Complex(*self)
        }
    }

    /// Returns the absolute value (magnitude) of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(3.0, 4.0);
    /// assert_eq!(c.abs(), 5.0);
    /// ```
    #[must_use]
    pub fn abs(&self) -> f64 {
        self.real.hypot(self.imaginary)
    }
    /// Returns the complex conjugate of the number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(1.0, 5.0);
    /// assert_eq!(c.conj(), ComplexNumber::new(1.0, -5.0));
    /// ```
    #[must_use]
    pub const fn conj(&self) -> Self {
        Self { real:      self.real,
               imaginary: -self.imaginary, }
    }
    /// Returns the reciprocal (1/z) of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(2.0, 0.0);
    /// assert!((c.recip().real - 0.5).abs() < 1e-10);
    /// assert!((c.recip().imaginary).abs() < 1e-10);
    /// ```
    #[must_use]
    pub const fn recip(&self) -> Self {
        let coj_squared = self.real * self.real + self.imaginary * self.imaginary;

        Self { real:      self.real / coj_squared,
               imaginary: -(self.imaginary / coj_squared), }
    }
    /// Returns the argument (phase angle) in radians.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(0.0, 1.0);
    /// assert!((c.arg() - std::f64::consts::FRAC_PI_2).abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn arg(self) -> f64 {
        self.imaginary.atan2(self.real)
    }
    /// Raises the complex number to an integer power.
    ///
    /// Performs repeated multiplication with overflow and division-by-zero
    /// checks.
    ///
    /// # Parameters
    /// - `exp`: The exponent (may be negative).
    /// - `line`: Source line number for error reporting.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::{ComplexNumber, ONE};
    /// let c = ComplexNumber::new(2.0, 0.0);
    /// assert_eq!(c.checked_powi(0, 0).unwrap(), ONE.into());
    /// assert_eq!(c.checked_powi(3, 0).unwrap(),
    ///            ComplexNumber::new(8.0, 0.0).into());
    /// ```
    pub fn checked_powi(self, exp: i64, line: usize) -> EvalResult<Value> {
        if exp == 0 {
            return Ok(ONE.into());
        }

        if self.real == 0.0 && self.imaginary == 0.0 && exp < 0 {
            return Err(RuntimeError::DivisionByZero { line });
        }

        let mut base = self;
        let mut result = ONE;
        let mut n = exp.abs();

        while n > 0 {
            if n % 2 == 1 {
                result *= base;
                if !result.real.is_finite() || !result.imaginary.is_finite() {
                    return Err(RuntimeError::Overflow { line });
                }
            }
            base = base * base;
            if !base.real.is_finite() || !base.imaginary.is_finite() {
                return Err(RuntimeError::Overflow { line });
            }
            n /= 2;
        }

        if exp < 0 {
            result = result.recip();
            if !result.real.is_finite() || !result.imaginary.is_finite() {
                return Err(RuntimeError::Overflow { line });
            }
        }

        Ok(result.into())
    }
    /// Raises the complex number to a floating-point power.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(4.0, 0.0);
    /// let res = c.powf(0.5);
    /// assert!((res.real - 2.0).abs() < 1e-10);
    /// assert!(res.imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn powf(self, exp: f64) -> Self {
        let r = self.abs();
        let theta = self.arg();

        let new_r = r.powf(exp);
        let new_theta = theta * exp;

        Self { real:      new_r * new_theta.cos(),
               imaginary: new_r * new_theta.sin(), }
    }
    /// Returns the principal square root of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let c = ComplexNumber::new(9.0, 0.0);
    /// let s = c.sqrt();
    /// assert!((s.real - 3.0).abs() < 1e-10);
    /// assert!(s.imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn sqrt(self) -> Self {
        let a = self.real;
        let b = self.imaginary;
        let r = a.hypot(b);

        let real = f64::midpoint(r, a).sqrt();
        let imaginary = ((r - a) / 2.0).sqrt().copysign(b); // preserve sign of b

        Self { real, imaginary }
    }
    /// Returns the sine of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!(z.sin().real.abs() < 1e-10);
    /// assert!(z.sin().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn sin(self) -> Self {
        Self { real:      self.real.sin() * self.imaginary.cosh(),
               imaginary: self.real.cos() * self.imaginary.sinh(), }
    }
    /// Returns the cosine of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!((z.cos().real - 1.0).abs() < 1e-10);
    /// assert!(z.cos().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn cos(self) -> Self {
        Self { real:      self.real.cos() * self.imaginary.cosh(),
               imaginary: -self.real.sin() * self.imaginary.sinh(), }
    }
    /// Returns the tangent of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!(z.tan().real.abs() < 1e-10);
    /// assert!(z.tan().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn tan(self) -> Self {
        self.sin() / self.cos()
    }
    /// Returns the hyperbolic sine of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!(z.sinh().real.abs() < 1e-10);
    /// assert!(z.sinh().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn sinh(self) -> Self {
        Self { real:      self.real.sinh() * self.imaginary.cos(),
               imaginary: self.real.cosh() * self.imaginary.sin(), }
    }
    /// Returns the hyperbolic cosine of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!((z.cosh().real - 1.0).abs() < 1e-10);
    /// assert!(z.cosh().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn cosh(self) -> Self {
        Self { real:      self.real.cosh() * self.imaginary.cos(),
               imaginary: self.real.sinh() * self.imaginary.sin(), }
    }
    /// Returns the hyperbolic tangent of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!(z.tanh().real.abs() < 1e-10);
    /// assert!(z.tanh().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn tanh(self) -> Self {
        self.sinh() / self.cosh()
    }
    /// Returns the exponential of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(0.0, 0.0);
    /// assert!((z.exp().real - 1.0).abs() < 1e-10);
    /// assert!(z.exp().imaginary.abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn exp(self) -> Self {
        let exp_r = self.real.exp();
        Self { real:      exp_r * self.imaginary.cos(),
               imaginary: exp_r * self.imaginary.sin(), }
    }
    /// Returns the natural logarithm (ln) of the complex number.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::value::complex::ComplexNumber;
    /// let z = ComplexNumber::new(1.0, 0.0);
    /// let ln = z.ln();
    /// assert!((ln.real).abs() < 1e-10); // ln(1) == 0
    /// assert!((ln.imaginary).abs() < 1e-10);
    /// ```
    #[must_use]
    pub fn ln(self) -> Self {
        Self { real:      self.abs().ln(),
               imaginary: self.arg(), }
    }
}

impl ops::Neg for ComplexNumber {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self { real:      -self.real,
               imaginary: -self.imaginary, }
    }
}

impl ops::Add for ComplexNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self { real:      self.real + rhs.real,
               imaginary: self.imaginary + rhs.imaginary, }
    }
}

impl ops::AddAssign for ComplexNumber {
    fn add_assign(&mut self, rhs: Self) {
        self.real += rhs.real;
        self.imaginary += rhs.imaginary;
    }
}

impl ops::Sub for ComplexNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self { real:      self.real - rhs.real,
               imaginary: self.imaginary - rhs.imaginary, }
    }
}

impl ops::Sub for &ComplexNumber {
    type Output = ComplexNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        ComplexNumber { real:      self.real - rhs.real,
                        imaginary: self.imaginary - rhs.imaginary, }
    }
}

impl ops::SubAssign for ComplexNumber {
    fn sub_assign(&mut self, rhs: Self) {
        self.real -= rhs.real;
        self.imaginary -= rhs.imaginary;
    }
}

impl ops::Mul for ComplexNumber {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self { real:      self.real
                              .mul_add(rhs.real, -(self.imaginary * rhs.imaginary)),
               imaginary: self.real.mul_add(rhs.imaginary, self.imaginary * rhs.real), }
    }
}

impl ops::MulAssign for ComplexNumber {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl ops::Div for ComplexNumber {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let denom = rhs.real.mul_add(rhs.real, rhs.imaginary * rhs.imaginary);
        Self { real:      self.real.mul_add(rhs.real, self.imaginary * rhs.imaginary) / denom,
               imaginary: self.imaginary
                              .mul_add(rhs.real, -(self.real * rhs.imaginary))
                          / denom, }
    }
}

impl ops::DivAssign for ComplexNumber {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<T> From<T> for ComplexNumber where T: Into<f64>
{
    fn from(value: T) -> Self {
        Self { real:      value.into(),
               imaginary: 0.0, }
    }
}

impl PartialEq for ComplexNumber {
    fn eq(&self, other: &Self) -> bool {
        OrderedFloat(self.real) == OrderedFloat(other.real)
        && OrderedFloat(self.imaginary) == OrderedFloat(other.imaginary)
    }
}

impl Eq for ComplexNumber {}

impl Hash for ComplexNumber {
    fn hash<H: Hasher>(&self, state: &mut H) {
        OrderedFloat(self.real).hash(state);
        OrderedFloat(self.imaginary).hash(state);
    }
}

impl PartialOrd for ComplexNumber {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ComplexNumber {
    fn cmp(&self, other: &Self) -> Ordering {
        let real_cmp = OrderedFloat(self.real).cmp(&OrderedFloat(other.real));
        if real_cmp == Ordering::Equal {
            OrderedFloat(self.imaginary).cmp(&OrderedFloat(other.imaginary))
        } else {
            real_cmp
        }
    }
}
