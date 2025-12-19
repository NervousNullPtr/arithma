use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
    util::num::i64_to_u32_checked,
};

impl Context {
    /// Evaluates an exponentiation operation.
    ///
    /// Integer–integer exponentiation uses checked arithmetic. Negative integer
    /// exponents are computed in floating-point form. Complex bases support
    /// both integer and real exponents. In all other cases, operands are
    /// promoted to real numbers and evaluated with `powf`.
    ///
    /// # Parameters
    /// - `base`: The base value.
    /// - `exponent`: The exponent value.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing the result of `base ^ exponent`.
    ///
    /// # Example
    /// ```
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let b = Value::Integer(2);
    /// let e = Value::Integer(10);
    /// let line = 1;
    ///
    /// let result = Context::eval_pow(&b, &e, line).unwrap();
    /// assert_eq!(result, Value::Integer(1024));
    /// ```
    pub fn eval_pow(base: &Value, exponent: &Value, line: usize) -> EvalResult<Value> {
        use Value::{Complex, Integer, Real};

        match (base, exponent) {
            (Integer(b), Integer(e)) => {
                if *e < 0 {
                    Ok(Real(base.as_real(line)?.powf(exponent.as_real(line)?)))
                } else {
                    b.checked_pow(i64_to_u32_checked(*e, line)?)
                     .map(Integer)
                     .ok_or(RuntimeError::Overflow { line })
                }
            },
            (Complex(b), Integer(e)) => b.checked_powi(*e, line),
            (Complex(b), Real(e)) => Ok(Complex(b.powf(*e))),
            _ => {
                let (l, r) = base.clone().promote_to_real(exponent, line)?;
                Ok(Real(l.as_real(line)?.powf(r.as_numeric_f64(line)?)))
            },
        }
    }
}
