use std::fs::{self};

use arithma::get_result;
use walkdir::WalkDir;

#[test]
fn book_examples_work() {
    let mut count = 0;

    for entry in
        WalkDir::new("book/src").into_iter()
                                .filter_map(Result::ok)
                                .filter(|e| e.path().extension().is_some_and(|ext| ext == "md"))
    {
        let path = entry.path();
        let content =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("Failed to read {path:?}: {e}"));

        for (i, code) in extract_dsl_blocks(&content).into_iter().enumerate() {
            count += 1;
            if let Err(e) = get_result(&code, false) {
                panic!("DSL example {} in {:?} failed:\n{}\nError: {:?}",
                       i + 1,
                       path,
                       code,
                       e);
            }
        }
    }

    assert!(count > 0, "No DSL examples found in book/src");
}

fn extract_dsl_blocks(content: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut inside = false;
    let mut buf = String::new();

    for line in content.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("```arithma") {
            inside = true;
            buf.clear();
            continue;
        }
        if inside && trimmed.starts_with("```") {
            inside = false;
            blocks.push(buf.clone());
            continue;
        }
        if inside {
            buf.push_str(line);
            buf.push('\n');
        }
    }

    blocks
}

fn assert_success(src: &str) {
    if let Err(e) = get_result(src, false) {
        panic!("Script failed: {e}");
    }
}

fn assert_failure(src: &str) {
    if get_result(src, false).is_ok() {
        panic!("Script succeeded but was expected to fail")
    }
}

#[test]
fn assignment_and_basic_arithmetic() {
    assert_success("let x = 1 + 2\nassert(x == 3)");
    assert_success("let x = 7 * 9\nassert(x == 63)");
    assert_success("let x = 8 - 5\nassert(x == 3)");
    assert_success("let x = 10 / 2\nassert(x == 5)");
}

#[test]
fn compound_assignments() {
    assert_success("let x = 2\nx += 3\nassert(x == 5)");
    assert_success("let x = 7\nx -= 2\nassert(x == 5)");
    assert_success("let x = 4\nx *= 2\nassert(x == 8)");
    assert_success("let x = 9\nx /= 3\nassert(x == 3)");
}

#[test]
fn builtin_functions_and_type_promotion() {
    assert_success("assert(sin(0) == 0)");
    assert_success("assert(|-5| == 5)");
    assert_success("let x = 9\nassert(sqrt(x) == 3)");
    assert_success("assert(round(3.7) == 4)");
    assert_success("assert(sign(-42) == -1)");
    assert_success("assert(sign(0) == 0)");
    assert_success("assert(sign(11) == 1)");
}

#[test]
fn user_defined_function_and_calls() {
    assert_success("square(x) = x * x\nassert(square(3) == 9)");
    assert_success("add(a, b) = a + b\nassert(add(2, 5) == 7)");
}

#[test]
fn factorial_and_multi_factorial() {
    assert_success("let x = 5!\nassert(x == 120)");
    assert_success("let y = 7!!\nassert(y == 105)");
    assert_success("let z = -4!\nassert(z == -24)");
}

#[test]
fn logical_and_comparisons() {
    assert_success("assert(2 < 3)");
    assert_success("assert(3 > 2)");
    assert_success("assert(2 <= 2)");
    assert_success("assert(3 >= 3)");
    assert_success("assert(2 != 3)");
    assert_success("assert(2 == 2)");
    assert_success("assert(!false)");
    assert_success("assert(true)");
    assert_success("assert(false == false)");
}

#[test]
fn if_else_and_blocks() {
    assert_success("let x = if 2 < 3 do { 7 } else do { 11 }\nassert(x == 7)");
    assert_success(
                   r#"
        let y = do {
            let a = 1
            let b = 2
            a + b
        }
        assert(y == 3)
    "#,
    );
}

#[test]
fn arrays_and_indexing() {
    assert_success("let a = [1, 2, 3]\nassert(a[0] == 1)\nassert(a[2] == 3)");
    assert_success("let b = [3, 2, 1]\nassert(b[1] == 2)");
}

#[test]
fn array_math_and_elementwise() {
    assert_success("let a = [1, 2, 3] * 2\nassert(a[2] == 6)");
    assert_success("let b = [4, 5, 6] + [1, 2, 3]\nassert(b[1] == 7)");
    assert_success("let c = [2, 4, 6] / 2\nassert(c[0] == 1)");
    assert_success("let d = 2 * [3, 4, 5]\nassert(d[2] == 10)");
}

#[test]
fn norm_and_abs_array() {
    assert_success("let v = [3, 4]\nassert(||v|| == 5)");
    assert_success("let v2 = [-3, -4]\nassert(||v2|| == 5)");
}

#[test]
fn for_loops_and_sum() {
    assert_success("let sum = 0\nfor x in 1..5 do { sum += x }\nassert(sum == 10)");
    assert_success("let sum = 0\nfor x in 1..=5 do { sum += x }\nassert(sum == 15)");
    assert_success("let arr = [2,3,4]\nlet sum = 0\nfor x in arr do { sum += x }\nassert(sum == 9)");
}

#[test]
fn complex_numbers() {
    assert_success("let c = 2 + 3i\nassert(conj(c) == 2 - 3i)");
    assert_success("assert((2 + 3i) ^ 2 == -5 + 12i)");
    assert_success("assert(ln(2 + 5i) ~ 1.6836479149932368 + 1.1902899496825317i)");
}

#[test]
fn matrix_and_elementwise() {
    assert_success("let a = [[1, 2], [3, 4]] * [[2, 2], [2, 2]]\nassert(a[0][1] == 4)");
}

#[test]
fn test_script_file() {
    let script = fs::read_to_string("tests/example.math").expect("missing file");
    assert_success(&script);
}

#[test]
fn division_by_zero_is_error() {
    assert_failure("let x = 1 / 0");
}

#[test]
fn unknown_variable_is_error() {
    assert_failure("assert(foo == 1)");
}

#[test]
fn redefinition_of_builtin_function_is_error() {
    assert_failure("sin(x) = x");
}

#[test]
fn wrong_function_arity_is_error() {
    assert_failure("f(x, y) = x + y\nf(3)");
}

#[test]
fn example_works() {
    let contents = fs::read_to_string("tests/example.math").unwrap();
    assert_success(&contents);
}
