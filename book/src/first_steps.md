# Chapter I: First steps.
The idea of arithma is that it's designed to be understood by reading it. This chapter introduces its notation through short examples and minimal explanation. The goal is to show how expressions, variables, and functions behave before discussing syntax and evaluation rules in detail.

## 1. Literals and Variables.
Numbers, booleans, and complex values can be written directly. Variable assignment uses `=`.
```arithma
let pi     = 3.141592653589793
let e      = 2.718281828459045
let radius = 5
```
Assignments are immutable by default. Reassigning a variable name creates a new binding in the current scope.

arithma follows standard mathematical precedence and allows compact arithmetic expressions.

```arithma
let pi     = 3.141592653589793
let e      = 2.718281828459045
let radius = 5

let area = pi * radius ^ 2
assert(area ~ 78.53981634)
let circumference = 2 * pi * radius
assert(circumference ~ 31.41592653589793)
```
Exponentiation uses `^`, and results follow floating-point semantics unless all operands are integers.

## 2. Compound assignments.
Compound operators modify an existing variable by applying an arithmetic operation.
```arithma
let radius = 2
radius += 2
assert(radius == 4)
```
This is equivalent to `radius = radius + 2`.

## 3. Built-in functions.
Common mathematical functions are available.
```arithma
let pi = 3.141592653589793
let e  = 2.718281828459045

assert(sin(pi / 2) ~ 1.0)
assert(sqrt(49) ~ 7.0)
assert(ln(e) ~ 1)
```
Functions return real or complex values depending on their arguments. arithma automatically promotes numeric types as needed.

## 4. Defining functions.
Functions are defined using a concise algebraic form.
```arithma
let pi = 3.141592653589793

circle_area(r) = pi * r ^ 2
```
They can be then called using the usual syntax:
```arithma
let pi = 3.141592653589793

circle_area(r) = pi * r ^ 2

assert(circle_area(10) ~ 314.1592653589793)
```
(The ~ operator checks approximate equality, suitable for floating-point comparisons.)

## 5. Control flow.
Conditional expressions use braces and are evaluated in place.
```arithma
custom_max(a, b) = if a > b do { a } else do { b }
assert(custom_max(42, 17) == 42)
```
For-loops iterate over ranges. The operator .. defines a semi-exclusive range to the right, and ..= defines a fully inclusive one.
```arithma
let sum = 0
for x in 1..5 do {
    sum += x
}
assert(sum == 10)

let sum_inc = 0
for x in 1..=5 do {
    sum_inc += x
}
assert(sum_inc == 15)
```

## 6. Blocks and scope.
Braces {} create a new block scope. Inner variables do not shadow or overwrite outer ones.
```arithma
let outer = 100
let result = do {
    let inner = 20
    outer + inner
}
assert(result == 120)
```

## 7. Complex numbers and vectors.
Complex numbers use the suffix i.
Vectors and matrices are written using brackets and support arithmetic operations.
```arithma
let complex = 2 + 5i
assert(conj(complex) == 2 - 5i)

let array = [1, 2, 3]
assert(array * 2 == [2, 4, 6])
```
Vector operations apply element-wise, and matrix multiplication follows standard linear-algebra rules. The latter is work in progress.

## 8. Assertions and testing.
`assert` validates expressions during execution.
For floating-point results, use `~` to compare within a tolerance, or specify one explicitly:
```arithma
assert(1 ~ 2, abs = 1.0)
```
Assertions are a convenient way to document and verify examples.
Most examples in this book include them so that they can be executed as tests.