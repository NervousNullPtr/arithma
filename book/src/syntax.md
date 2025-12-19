# Chapter II: Syntax and expressions
arithma programs are sequences of expressions. Each expression evaluates to a value.
Every construct in the language reduces to a value through evaluation.

## 1. Lexical elements
Whitespace separates tokens but has no syntactic meaning.
Identifiers consist of letters, digits, and underscores, and must not begin with a digit.
Comments begin with // and extend to the end of the line.
```arithma
// This is a comment.
let r = 2
let radius_squared = r^2 // r squared
```

### a. Identifiers
Identifiers are names for variables and functions.
They consist of letters, digits, and underscores, but may not begin with a digit.
```arithma
let area_total = 42
calculate_radius() = sqrt(area_total / pi)
```

### b. Literals
Literals represent constant values.
Supported literal types include:
| Kind           | Example                        | Description                                  |
| -------------- | ------------------------------ | -------------------------------------------- |
| Integer        | `42`                           | 64-bit signed integer                        |
| Real           | `3.1415`                       | 64-bit floating-point                        |
| Complex        | `2 + 3i`                       | Complex number with real and imaginary parts |
| Boolean        | `true`, `false`                | Logical values                               |
| String         | `"hello"`                      | Optional; may be used in diagnostic messages |
| Array / Matrix | `[1, 2, 3]` or `[[1,2],[3,4]]` | Homogeneous array of values                  |
| Set            | `{1, 2, 3}`                    | Collection of unique values                  |
Numeric types automatically promote when mixed (integer to real to complex).

## 2. Expressions
Expressions combine values, variables, and operators to produce results.
```arithma
let a = 5
let b = 2
let result = (a + b) * 3
```
Parentheses can be used to override precedence.

### a. Operator precedence and associativity
Operators follow conventional mathematical precedence.
From highest to lowest:
| Precedence | Operator                              | Meaning                                                  | Associativity |
| ---------- | ------------------------------------- | -------------------------------------------------------- | ------------- |
| 1          | `f(x)`                                | Function call                                            | Left          |
| 2          | `^`                                   | Exponentiation                                           | Right         |
| 3          | `*`, `/`, `%`, `@`                    | Multiplication, division, modulus, matrix multiplication | Left          |
| 4          | `+`, `-`                              | Addition, subtraction                                    | Left          |
| 5          | `<`, `<=`, `>`, `>=`, `==`, `!=`, `~` | Comparison and approximate equality                      | None          |
| 6          | `and`, `or`, `not`                    | Logical junctions                                        | Left          |
| 7          | `=`                                   | Assignment                                               | Right         |
| 8          | `+=`, `-=`, `*=`, `/=`                | Compound assignment                                      | Right         |
The matrix multiplication operator @ follows standard linear algebra semantics.
It contracts the last dimension of the left operand with the second-to-last of the right operand.

### b. Compound/Unary operators
| Operator  | Example      | Meaning          |
| --------- | ------------ | ---------------- |
| `+=`      | `x += 1`     | `x = x + 1`      |
| `-=`      | `x -= 1`     | `x = x - 1`      |
| `*=`      | `x *= 2`     | `x = x * 2`      |
| `/=`      | `x /= 2`     | `x = x / 2`      |
| `%=`      | `x %= 3`     | `x = x % 3`      |
| `@=`      | `A @= B`     | `A = A @ B`      |
| Unary `-` | `-x`         | Negation         |
| Unary `!` | `!condition` | Logical negation |

## 3. Arrays and Sets
Arrays and matrices use square brackets `[...]`.
```arithma
let v = [1, 2, 3]
let M = [[1, 2], [3, 4]]
```
Operations between arrays are element-wise when shapes match.
Matrix multiplication uses the @ operator.
```arithma
let A = [[1, 2], [3, 4]]
let B = [[5, 6], [7, 8]]
let C = A @ B // [[19, 22], [43, 50]]
```
Sets use curly braces `{...}` and contain unique, unordered elements.
```arithma
let S = {1, 2, 2, 3}
assert(S == {1, 2, 3})
```
Set operations use dedicated operators:
| Operation            | Symbol | Example                        |
| -------------------- | ------ | ------------------------------ |
| Union                | `|`    | `{1,2} | {2,3}` = `{1,2,3}`    |
| Intersection         | `&`    | `{1,2,3} & {2,3,4}` = `{2,3}`  |
| Difference           | `-`    | `{1,2,3} - {2}` = `{1,3}`      |
| Symmetric difference | `^`    | `{1,2} ^ {2,3}` = `{1,3}`      |

## 4. Function definitions
Functions are first-class and defined with a concise syntax:
```arithma
square(x) = x ^ 2
```

Multiple arguments use commas and blocks can serve as function bodies:
```arithma
custom_max(a, b) = if a > b do { a } else do { b }
```
Functions are immutable.
## 5. Code control structures
### a. If-expressions
`if` returns the value of the branch it evaluates.
```arithma
let n = 1
let x = if n > 0 do { n } else do { -n } // evaluates to the value of 'n'
```
### b. For-loops
`for` iterates over ranges or collections of values.
```arithma
let sum = 0
for x in 1..=10 do {
    sum += i
}
```
The loop’s final expression is procedural and has no return value.
## 6. Blocks
Blocks `{...}` introduce new lexical scopes.
Variables defined inside are local to that block.
```arithma
let a = 10
let b = do {
    let a = 5
    a * 2
}
assert(b == 10)
assert(a == 10)
```
## 7. Assertions, Errors
arithma reports runtime errors with context and line numbers.
Assertions `(assert(expr))` are used for testing and validation.
```arithma
assert(2 + 2 == 4)
assert(1 ~ 1.0001, abs = 0.001)
```
Errors halt execution; assertions can be used to define verifiable examples in documentation.