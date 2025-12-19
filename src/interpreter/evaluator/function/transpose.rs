use crate::{
    error::RuntimeError,
    interpreter::{
        evaluator::{binary::matmul::shape_of, core::EvalResult, utils::check_arity},
        value::core::Value,
    },
};

/// Transposes an array by swapping its first two dimensions.
///
/// The function supports array values of any depth.
/// - Scalars are rejected.
/// - A 1-dimensional array `[x₀, x₁, …, xₙ]` produces `n` empty rows.
/// - Higher-dimensional arrays are treated structurally as a 2-dimensional
///   table of cells, and only the outer two axes are transposed.
///
/// Inner array contents are not modified or recursively processed.
///
/// # Parameters
/// - `args`: Slice containing exactly one array value.
/// - `line`: Line number for error reporting.
///
/// # Returns
/// `Some(Value::Array)` containing the transposed structure.
///
/// # Example
/// ```
/// use arithma::interpreter::{evaluator::function::transpose::transpose, value::core::Value};
///
/// // [[1,2],[3,4]] -> [[1,3],[2,4]]
/// let input =
///     Value::Array(vec![Value::Array(vec![Value::Integer(1), Value::Integer(2)].into()),
///                       Value::Array(vec![Value::Integer(3), Value::Integer(4)].into()),].into());
///
/// let r = transpose(&[input], 1).unwrap();
///
/// let expected = Value::Array(vec![Value::Array(vec![Value::Integer(1),
///                                               Value::Integer(3)].into()),
///                                  Value::Array(vec![Value::Integer(2),
///                                               Value::Integer(4)].into()),].into());
///
/// assert_eq!(r, expected);
///
/// // 1D array: [1,2] -> [[1],[2]]
/// let input_1d = Value::Array(vec![Value::Integer(1), Value::Integer(2)].into());
///
/// let r1 = transpose(&[input_1d], 1).unwrap();
///
/// let expected_1d =
///     Value::Array(vec![Value::Array(vec![Value::Integer(1)].into()),
///                       Value::Array(vec![Value::Integer(2)].into()),].into());
///
/// assert_eq!(r1, expected_1d);
/// ```
pub fn transpose(args: &[Value], line: usize) -> EvalResult<Value> {
    use crate::interpreter::value::core::Value;

    check_arity(args, 1, line)?;
    let input = &args[0];

    let shape = shape_of(input, line)?;

    if shape.is_empty() {
        return Err(RuntimeError::TypeError { details:
                                                 "Scalar values cannot be transposed".to_string(),
                                             line });
    }

    if shape.len() == 1 {
        let values = input.as_vec(line)?;
        let mut result = Vec::with_capacity(values.len());

        for item in values {
            result.push(Value::Array(vec![item.clone()].into()));
        }

        return Ok(Value::Array(result.into()));
    }

    let rows = shape[0];
    let columns = shape[1];

    let row_values = input.as_vec(line)?;
    let mut column_values: Vec<Vec<Value>> =
        (0..columns).map(|_| Vec::with_capacity(rows)).collect();

    for row in row_values {
        let elements = row.as_vec(line)?;
        for (column_vector, element) in column_values.iter_mut().zip(elements.iter()) {
            column_vector.push(element.clone());
        }
    }

    let result: Vec<Value> = column_values.into_iter()
                                          .map(|column| Value::Array(column.into()))
                                          .collect();

    Ok(Value::Array(result.into()))
}
