use std::{
    collections::HashSet,
    fmt::Display,
    hash::{Hash, Hasher},
    rc::Rc,
};

use ordered_float::OrderedFloat;

use crate::interpreter::value::{complex::ComplexNumber, core::Value};

/// Enum representing values allowed in sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SetValue {
    /// An integer such as `-4` or `42`.
    Integer(i64),
    /// A boolean such as `true`.
    Bool(bool),
    /// A real such as `3.141592653589793`.
    Real(OrderedFloat<f64>),
    /// A complex number such as `2i`.
    Complex(ComplexNumber),
    /// An array such as `[1, 2, 2]`.
    Array(Vec<SetValue>),
    /// A set such as `{1, 2, true}`.
    Set(HashSet<SetValue>),
}

impl From<&Value> for SetValue {
    fn from(v: &Value) -> Self {
        match v {
            Value::Integer(i) => Self::Integer(*i),
            Value::Bool(b) => Self::Bool(*b),
            Value::Real(r) => Self::Real(OrderedFloat(*r)),
            Value::Complex(c) => Self::Complex(*c),
            Value::Array(arr) => Self::Array(arr.iter().map(Self::from).collect()),
            Value::Set(set) => Self::Set(set.iter().cloned().collect()),
        }
    }
}

impl From<SetValue> for Value {
    fn from(s: SetValue) -> Self {
        match s {
            SetValue::Integer(i) => Self::Integer(i),
            SetValue::Bool(b) => Self::Bool(b),
            SetValue::Real(r) => Self::Real(r.into_inner()),
            SetValue::Complex(c) => Self::Complex(c),
            SetValue::Array(arr) => Self::Array(Rc::new(arr.into_iter().map(Self::from).collect())),
            SetValue::Set(set) => Self::Set(Rc::new(set.into_iter().collect())),
        }
    }
}

impl Hash for SetValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use SetValue::{Array, Bool, Complex, Integer, Real, Set};
        match self {
            Integer(i) => {
                state.write_u8(0);
                i.hash(state);
            },
            Bool(b) => {
                state.write_u8(1);
                b.hash(state);
            },
            Real(r) => {
                state.write_u8(2);
                r.hash(state);
            },
            Complex(c) => {
                state.write_u8(3);
                c.hash(state);
            },
            Array(arr) => {
                state.write_u8(4);
                arr.hash(state);
            },
            Set(set) => {
                state.write_u8(5);
                let mut hashes: Vec<u64> =
                    set.iter()
                       .map(|item| {
                           let mut hasher = std::collections::hash_map::DefaultHasher::new();
                           item.hash(&mut hasher);
                           hasher.finish()
                       })
                       .collect();

                hashes.sort_unstable();

                let mut combined_hash: u64 = 0;
                for h in hashes {
                    combined_hash = combined_hash.wrapping_add(h);
                }
                combined_hash.hash(state);
            },
        }
    }
}

impl Display for SetValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let value: Value = self.clone().into();
        write!(f, "{value}")
    }
}
