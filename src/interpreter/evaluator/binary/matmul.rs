use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::core::{Context, EvalResult},
        value::core::Value,
    },
};

impl Context {
    /// Evaluates matrix multiplication using the `@` operator.
    ///
    /// Both operands must be arrays. The function supports vector–vector,
    /// matrix–vector, vector–matrix and general n-dimensional batched
    /// multiplication. Shape compatibility is checked before dispatching to the
    /// appropriate multiplication routine.
    ///
    /// # Shape rules
    /// - `1D @ 1D` produces a scalar via dot product.
    /// - `2D @ 1D` produces a 1D vector.
    /// - `1D @ 2D` produces a 1D vector.
    /// - Higher-dimensional arrays require the last dimension of the left array
    ///   to match the second-to-last dimension of the right array. Batch
    ///   dimensions are broadcast using `broadcast_shapes`.
    ///
    /// # Parameters
    /// - `left`: Left operand.
    /// - `right`: Right operand.
    /// - `line`: Line number for error reporting.
    ///
    /// # Returns
    /// An `EvalResult<Value>` containing the resulting array.
    ///
    /// # Example
    /// ```
    /// use std::rc::Rc;
    ///
    /// use arithma::interpreter::{evaluator::core::Context, value::core::Value};
    ///
    /// let a = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Real(1.0),
    ///                                                             Value::Real(2.0)])),
    ///                                   Value::Array(Rc::new(vec![Value::Real(3.0),
    ///                                                             Value::Real(4.0)])),]));
    ///
    /// let b = Value::Array(Rc::new(vec![Value::Real(1.0), Value::Real(2.0)]));
    ///
    /// let result = Context::eval_matmul(&a, &b, 1);
    ///
    /// // Matrix–vector multiplication: [ [1,2], [3,4] ] @ [1,2] = [5,11]
    /// assert!(result.is_ok());
    /// ```
    pub fn eval_matmul(left: &Value, right: &Value, line: usize) -> EvalResult<Value> {
        if !left.is_array() || !right.is_array() {
            return Err(RuntimeError::TypeError { details: format!("@ expects arrays, got {left} and {right}"),
                                                 line });
        }
        let lshape = shape_of(left, line)?;
        let rshape = shape_of(right, line)?;

        if lshape.len() == 1 && rshape.len() == 1 {
            // 1D * 1D => scalar
            if lshape[0] != rshape[0] {
                return Err(dim_mismatch(&lshape, &rshape, line));
            }
            return dot_1d_1d(left, right, line);
        }

        if lshape.len() == 2 && rshape.len() == 1 {
            // 2D * 1D => 1D
            if lshape[1] != rshape[0] {
                return Err(dim_mismatch(&lshape, &rshape, line));
            }
            return mat_2d_vec_1d(left, right, line);
        }

        if lshape.len() == 1 && rshape.len() == 2 {
            // 1D * 2D => 1D
            if lshape[0] != rshape[0] {
                return Err(dim_mismatch(&lshape, &rshape, line));
            }
            return vec_1d_mat_2d(left, right, line);
        }

        if lshape.len() < 2 || rshape.len() < 2 {
            return Err(RuntimeError::TypeError { details: format!("Cannot apply @ to shapes {lshape:?} and {rshape:?}"),
                                                 line });
        }

        let k_l = lshape[lshape.len() - 1];
        let k_r = rshape[rshape.len() - 2];
        if k_l != k_r {
            return Err(dim_mismatch(&lshape, &rshape, line));
        }

        let batch_l = &lshape[..lshape.len() - 2];
        let batch_r = &rshape[..rshape.len() - 2];
        let batch = broadcast_shapes(batch_l, batch_r).ok_or_else(|| RuntimeError::TypeError {
            details: format!("Cannot broadcast {batch_l:?} and {batch_r:?}"),
            line,
        })?;

        let out = matmul_nd(left, &lshape, right, &rshape, &batch, line)?;
        Ok(out)
    }
}

/// Computes the tensor shape of a value.
///
/// Scalars have shape `[]`. Arrays are treated as tensors, and their shape is
/// determined recursively based on the shape of their elements. All elements
/// must have the same shape. Ragged arrays are rejected.
/// Sets do not have shapes and produce a type error.
///
/// # Parameters
/// - `value`: The value whose shape is computed.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// An `EvalResult<Vec<usize>>` representing the shape.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::shape_of, value::core::Value};
///
/// // Shape: [2, 2]
/// let arr = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(1),
///                                                               Value::Integer(2)])),
///                                     Value::Array(Rc::new(vec![Value::Integer(3),
///                                                               Value::Integer(4)])),]));
///
/// let shape = shape_of(&arr, 1).unwrap();
/// assert_eq!(shape, vec![2, 2]);
/// ```
pub fn shape_of(value: &Value, line: usize) -> EvalResult<Vec<usize>> {
    match value {
        Value::Array(a) => {
            if a.is_empty() {
                return Ok(vec![0]);
            }
            let sub = shape_of(&a[0], line)?;
            for x in a.iter().skip(1) {
                if shape_of(x, line)? != sub {
                    return Err(RuntimeError::TypeError {
                        details: "Ragged arrays are not supported".into(),
                        line,
                    });
                }
            }
            let mut s = vec![a.len()];
            s.extend(sub);
            Ok(s)
        },
        Value::Real(_) | Value::Integer(_) | Value::Bool(_) | Value::Complex(_) => Ok(vec![]),
        Value::Set(_) => Err(RuntimeError::TypeError { details:
                                                           "Sets do not have a tensor shape".into(),
                                                       line }),
    }
}

/// Computes the broadcasted shape of two tensor shapes.
///
/// Broadcasting follows standard rules: shapes are aligned from the end,
/// and each dimension must match or one of them must be `1`.
/// If any dimension is incompatible, the function returns `None`.
/// The output shape contains the maximum along each broadcasted axis.
///
/// # Parameters
/// - `a`: First shape.
/// - `b`: Second shape.
///
/// # Returns
/// `Some(Vec<usize>)` with the broadcasted shape, or `None` if broadcasting is
/// not possible.
///
/// # Example
/// ```
/// use arithma::interpreter::evaluator::binary::matmul::broadcast_shapes;
///
/// // [2, 3] and [1, 3] can be broadcast to [2, 3]
/// let a = vec![2, 3];
/// let b = vec![1, 3];
/// assert_eq!(broadcast_shapes(&a, &b), Some(vec![2, 3]));
///
/// // [4, 1, 5] and [1, 7, 5] broadcast to [4, 7, 5]
/// let a = vec![4, 1, 5];
/// let b = vec![1, 7, 5];
/// assert_eq!(broadcast_shapes(&a, &b), Some(vec![4, 7, 5]));
///
/// // Incompatible shapes
/// let a = vec![2, 3];
/// let b = vec![3, 2];
/// assert_eq!(broadcast_shapes(&a, &b), None);
/// ```
#[must_use]
pub fn broadcast_shapes(a: &[usize], b: &[usize]) -> Option<Vec<usize>> {
    let mut out = Vec::new();
    let max = a.len().max(b.len());

    for i in 0..max {
        let ad = *a.get(a.len().wrapping_sub(i + 1)).unwrap_or(&1);
        let bd = *b.get(b.len().wrapping_sub(i + 1)).unwrap_or(&1);
        if ad == bd || ad == 1 || bd == 1 {
            out.push(ad.max(bd));
        } else {
            return None;
        }
    }
    out.reverse();
    Some(out)
}

/// Multiplies two scalar values.
///
/// This is a convenience wrapper around `Context::eval_scalar_op` using the
/// `Mul` operator. Both operands must be scalar types. Any required type
/// promotion is handled by the scalar operator machinery.
///
/// # Parameters
/// - `left`: Left operand.
/// - `right`: Right operand.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// An `EvalResult<Value>` containing the product.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::binary::matmul::mul_values, value::core::Value};
///
/// let x = Value::Integer(6);
/// let y = Value::Integer(7);
///
/// let result = mul_values(&x, &y, 1);
/// assert_eq!(result.unwrap(), Value::Integer(42));
/// ```
pub fn mul_values(left: &Value, right: &Value, line: usize) -> EvalResult<Value> {
    crate::Context::eval_scalar_op(crate::ast::BinaryOperator::Mul, left, right, line)
}

/// Adds two scalar values.
///
/// This is a convenience wrapper around `Context::eval_scalar_op` using the
/// `Add` operator. Both operands must be scalar types. Promotion rules are
/// applied automatically to match types before addition.
///
/// # Parameters
/// - `left`: Left operand.
/// - `right`: Right operand.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// An `EvalResult<Value>` containing the sum.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::binary::matmul::add_values, value::core::Value};
///
/// let a = Value::Real(1.5);
/// let b = Value::Real(2.0);
///
/// let result = add_values(&a, &b, 1);
/// assert_eq!(result.unwrap(), Value::Real(3.5));
/// ```
pub fn add_values(left: &Value, right: &Value, line: usize) -> EvalResult<Value> {
    crate::Context::eval_scalar_op(crate::ast::BinaryOperator::Add, left, right, line)
}
/// Computes the dot product of two 1D arrays.
///
/// Both operands must be vectors of equal length. The dot product is computed
/// by multiplying corresponding elements and then summing the products.
/// Accumulation uses `reduce_sum`.
///
/// # Parameters
/// - `left`: Left vector.
/// - `right`: Right vector.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// A scalar `Value`.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::dot_1d_1d, value::core::Value};
///
/// let v1 = Value::Array(Rc::new(vec![Value::Integer(1), Value::Integer(2)]));
/// let v2 = Value::Array(Rc::new(vec![Value::Integer(3), Value::Integer(4)]));
///
/// let r = dot_1d_1d(&v1, &v2, 1).unwrap();
///
/// assert_eq!(r, Value::Integer(11));
/// ```
pub fn dot_1d_1d(left: &Value, right: &Value, line: usize) -> EvalResult<Value> {
    let left_vector = left.as_vec(line)?;
    let right_vector = right.as_vec(line)?;

    reduce_sum(pairwise_mul(left_vector, right_vector, line), line)
}

/// Multiplies a 2D matrix with a 1D vector.
///
/// The matrix must have rows whose length matches the vector length. Each row
/// is combined with the vector using a dot-product style accumulation.
///
/// # Parameters
/// - `matrix`: 2D array.
/// - `vector`: 1D array.
/// - `line`: Line number.
///
/// # Returns
/// A 1D vector.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::mat_2d_vec_1d, value::core::Value};
///
/// let m = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(1),
///                                                             Value::Integer(2)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(3),
///                                                             Value::Integer(4)]))]));
///
/// let v = Value::Array(Rc::new(vec![Value::Integer(10), Value::Integer(20)]));
///
/// let r = mat_2d_vec_1d(&m, &v, 1).unwrap();
///
/// assert_eq!(r,
///            Value::Array(Rc::new(vec![Value::Integer(50), Value::Integer(110)])));
/// ```
pub fn mat_2d_vec_1d(matrix: &Value, vector: &Value, line: usize) -> EvalResult<Value> {
    let rows = matrix.as_vec(line)?;
    let x = vector.as_vec(line)?;

    let mut out = Vec::with_capacity(rows.len());

    for row in rows {
        let right_vector = row.as_vec(line)?;
        let sum = reduce_sum(pairwise_mul(right_vector, x, line), line)?;
        out.push(sum);
    }

    Ok(Value::Array(out.into()))
}

/// Multiplies a 1D vector with a 2D matrix.
///
/// The vector length must match the number of rows in the matrix. Each output
/// element is the dot product of the vector and a matrix column.
///
/// # Parameters
/// - `vector`: 1D array.
/// - `matrix`: 2D array.
/// - `line`: Line number.
///
/// # Returns
/// A 1D array.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::vec_1d_mat_2d, value::core::Value};
///
/// let v = Value::Array(Rc::new(vec![Value::Integer(1), Value::Integer(2)]));
///
/// let m = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(3),
///                                                             Value::Integer(4)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(5),
///                                                             Value::Integer(6)])),]));
///
/// let r = vec_1d_mat_2d(&v, &m, 1).unwrap();
///
/// assert_eq!(r,
///            Value::Array(Rc::new(vec![Value::Integer(13), Value::Integer(16)])));
/// ```
pub fn vec_1d_mat_2d(vector: &Value, matrix: &Value, line: usize) -> EvalResult<Value> {
    let x = vector.as_vec(line)?;
    let rows = matrix.as_vec(line)?;

    let n = rows.first()
                .map(|r| r.as_vec(line).map(Vec::len))
                .transpose()?
                .unwrap_or(0);

    let mut out = Vec::with_capacity(n);

    for col in 0..n {
        let col_items = rows.iter().enumerate().map(|(i, row)| {
                                                   let right_vector = row.as_vec(line)?;
                                                   mul_values(&x[i], &right_vector[col], line)
                                               });

        let sum = reduce_sum(col_items, line)?;
        out.push(sum);
    }

    Ok(Value::Array(out.into()))
}

/// Performs n-dimensional batched matrix multiplication.
///
/// This dispatcher handles all base cases directly:
/// - `1D @ 1D` uses `dot_1d_1d`.
/// - `2D @ 1D` uses `mat_2d_vec_1d`.
/// - `1D @ 2D` uses `vec_1d_mat_2d`.
/// - `2D @ 2D` uses `mat_2d_2d`.
///
/// For higher-rank tensors, the function iterates over the batch dimension,
/// slices both operands using `slice_along_batch` and recursively multiplies
/// the sub-tensors. The results are collected into a new array whose shape
/// matches the computed batch structure.
///
/// # Parameters
/// - `left`: Left operand.
/// - `left_shape`: Shape of the left operand.
/// - `right`: Right operand.
/// - `right_shape`: Shape of the right operand.
/// - `batch_shape`: Broadcasted batch dimensions.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// An `EvalResult<Value>` containing the batched product.
///
/// # Example
/// ```
/// // For simple cases the base-case dispatch is used.
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::matmul_nd, value::core::Value};
///
/// let a = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(1),
///                                                             Value::Integer(2)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(3),
///                                                             Value::Integer(4)])),]));
///
/// let b = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(5),
///                                                             Value::Integer(6)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(7),
///                                                             Value::Integer(8)])),]));
///
/// let result = matmul_nd(&a, &[2, 2], &b, &[2, 2], &[], 1).unwrap();
/// assert!(matches!(result, Value::Array(_)));
/// ```
pub fn matmul_nd(left: &Value,
                 left_shape: &[usize],
                 right: &Value,
                 right_shape: &[usize],
                 batch_shape: &[usize],
                 line: usize)
                 -> EvalResult<Value> {
    match (left_shape.len(), right_shape.len()) {
        (1, 1) => return dot_1d_1d(left, right, line),
        (2, 1) => return mat_2d_vec_1d(left, right, line),
        (1, 2) => return vec_1d_mat_2d(left, right, line),
        (2, 2) => return mat_2d_2d(left, right, line),
        _ => {},
    }

    let (b0, rest) = batch_shape.split_first().unwrap_or((&1, &[]));
    let mut chunks = Vec::with_capacity(*b0);

    for b_i in 0..*b0 {
        let left_slice = slice_along_batch(left, left_shape, batch_shape, b_i, line)?;
        let right_slice = slice_along_batch(right, right_shape, batch_shape, b_i, line)?;
        let result = matmul_nd(&left_slice.value,
                               &left_slice.shape,
                               &right_slice.value,
                               &right_slice.shape,
                               rest,
                               line)?;
        chunks.push(result);
    }

    Ok(Value::Array(chunks.into()))
}

/// Multiplies two 2D matrices.
///
/// The inner dimensions must match. Each resulting entry is the dot product
/// of a row of the left matrix with a column of the right matrix.
///
/// # Parameters
/// - `left`: Left matrix.
/// - `right`: Right matrix.
/// - `line`: Line number.
///
/// # Returns
/// A 2D array.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::mat_2d_2d, value::core::Value};
///
/// let a = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(1),
///                                                             Value::Integer(2)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(3),
///                                                             Value::Integer(4)])),]));
///
/// let b = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(5),
///                                                             Value::Integer(6)])),
///                                   Value::Array(Rc::new(vec![Value::Integer(7),
///                                                             Value::Integer(8)])),]));
///
/// let r = mat_2d_2d(&a, &b, 1).unwrap();
///
/// assert!(matches!(r, Value::Array(_)));
/// ```
pub fn mat_2d_2d(left: &Value, right: &Value, line: usize) -> EvalResult<Value> {
    let left_rows = left.as_vec(line)?;
    let right_rows = right.as_vec(line)?;

    let m = left_rows.len();
    let k = left_rows[0].as_vec(line)?.len();
    let n = right_rows[0].as_vec(line)?.len();

    let mut out_rows = Vec::with_capacity(m);

    for row in left_rows {
        let rv = row.as_vec(line)?;

        let mut out_row = Vec::with_capacity(n);

        for col in 0..n {
            let col_items = (0..k).map(|i| {
                                      let rv_row = rv[i].clone();
                                      let r_col_elem = right_rows[i].as_vec(line)?[col].clone();
                                      mul_values(&rv_row, &r_col_elem, line)
                                  });

            let sum = reduce_sum(col_items, line)?;
            out_row.push(sum);
        }

        out_rows.push(Value::Array(out_row.into()));
    }

    Ok(Value::Array(out_rows.into()))
}

pub struct Slice {
    pub value: Value,
    pub shape: Vec<usize>,
}

/// Extracts a slice of a batched tensor along the batch dimensions.
///
/// The function walks through the batch part of the shape, selecting either
/// the provided `index` or `0` for broadcasted dimensions (dimension equal
/// to 1). Each step descends one level into the nested array structure.
/// When all batch dimensions are consumed, the remaining value and shape are
/// returned unchanged.
///
/// # Example
/// ```
/// use std::rc::Rc;
///
/// use arithma::interpreter::{evaluator::binary::matmul::slice_along_batch, value::core::Value};
///
/// let tensor = Value::Array(Rc::new(vec![Value::Array(Rc::new(vec![Value::Integer(1),
///                                                                  Value::Integer(2)])),
///                                        Value::Array(Rc::new(vec![Value::Integer(3),
///                                                                  Value::Integer(4)])),]));
///
/// let shape = vec![2, 2];
/// let batch = vec![2];
///
/// let slice = slice_along_batch(&tensor, &shape, &batch, 1, 1).unwrap();
///
/// // With batch=[2], no batch dimensions exist in shape=[2,2],
/// // so the slice is the full tensor.
/// assert_eq!(slice.value, tensor);
/// assert_eq!(slice.shape, shape);
/// ```
pub fn slice_along_batch(mut value: &Value,
                         mut shape: &[usize],
                         target_batch: &[usize],
                         index: usize,
                         line: usize)
                         -> EvalResult<Slice> {
    if target_batch.is_empty() {
        return Ok(Slice { value: value.clone(),
                          shape: shape.to_vec(), });
    }

    let batch_rank = shape.len().saturating_sub(2);

    for depth in 0..batch_rank {
        let dimension = shape[depth];
        let pick = if dimension == 1 { 0 } else { index };

        let value_vec = value.as_vec(line)?;
        if pick >= value_vec.len() {
            return Err(RuntimeError::TypeError { details: format!("Batch index {pick} out of bounds for dimension {dimension}"),
                                                 line });
        }

        value = &value_vec[pick];
        shape = &shape[depth + 1..];
    }

    Ok(Slice { value: value.clone(),
               shape: shape.to_vec(), })
}

/// Creates a dimension-mismatch error for incompatible shapes.
///
/// # Parameters
/// - `left`: Left-hand shape.
/// - `right`: Right-hand shape.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// A `RuntimeError` describing the mismatch.
///
/// # Example
/// ```
/// use arithma::interpreter::evaluator::binary::matmul::dim_mismatch;
///
/// let err = dim_mismatch(&[2, 3], &[4, 3], 1);
/// assert!(format!("{err:?}").contains("Dimension mismatch"));
/// ```
#[must_use]
pub fn dim_mismatch(left: &[usize], right: &[usize], line: usize) -> RuntimeError {
    RuntimeError::TypeError { details: format!("Dimension mismatch: left shape {left:?}, right shape {right:?}"),
                              line }
}

/// Reduces a sequence of numeric values using addition.
///
/// Each item in the iterator must yield a `Value` or a `RuntimeError`.
/// The first element becomes the initial accumulator so that no unnecessary
/// addition happens for the first value. If the iterator is empty the result
/// is `Value::Integer(0)`.
///
/// # Parameters
/// - `items`: Iterator producing `EvalResult<Value>`.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// The accumulated result.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::binary::matmul::reduce_sum, value::core::Value};
///
/// let values = vec![Value::Integer(1), Value::Integer(2), Value::Integer(3)];
///
/// let r = reduce_sum(values.into_iter().map(Ok), 1).unwrap();
///
/// assert_eq!(r, Value::Integer(6));
/// ```
pub fn reduce_sum<I>(items: I, line: usize) -> EvalResult<Value>
    where I: Iterator<Item = EvalResult<Value>>
{
    let mut acc = None;

    for v in items {
        let v = v?;
        acc = Some(match acc {
                       Some(existing) => add_values(&existing, &v, line)?,
                       None => v,
                   });
    }

    Ok(acc.unwrap_or(Value::Integer(0)))
}

/// Creates an iterator that multiplies corresponding elements from two slices.
///
/// Both slices must have equal length. Each produced value is a scalar product
/// using `mul_values`.
///
/// # Parameters
/// - `a`: Left operands.
/// - `b`: Right operands.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// Iterator producing `EvalResult<Value>`.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::binary::matmul::pairwise_mul, value::core::Value};
///
/// let a = vec![Value::Integer(1), Value::Integer(2)];
/// let b = vec![Value::Integer(10), Value::Integer(20)];
///
/// let mut it = pairwise_mul(&a, &b, 1);
///
/// assert_eq!(it.next().unwrap().unwrap(), Value::Integer(10));
/// assert_eq!(it.next().unwrap().unwrap(), Value::Integer(40));
/// assert!(it.next().is_none());
/// ```
pub fn pairwise_mul<'a>(a: &'a [Value],
                        b: &'a [Value],
                        line: usize)
                        -> impl Iterator<Item = EvalResult<Value>> + 'a {
    a.iter()
     .zip(b.iter())
     .map(move |(x, y)| mul_values(x, y, line))
}
