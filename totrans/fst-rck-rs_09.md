# Variables

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/variables.html](https://freddiehaddad.github.io/fast-track-to-rust/variables.html)

Rust is a statically typed language, meaning that all variables have a type, and this type must be known at compile time. The `let` keyword is used to declare variables, or more precisely, for variable binding.

The anatomy of a `let` statement^([1](#footnote-1)) ^([2](#footnote-2)):

[PRE0]

## [Type Inference](#type-inference)

Since `y` is passed as an argument to the `print_value` function, which requires a signed 32-bit integer, the compiler infers its type. Therefore, the explicit type declaration for `x` can be omitted.

[PRE1]

## [Rustle Variables](#rustle-variables)

To begin with our rustle program, we'll avoid handling user input via command line arguments for now. Instead, we'll hard code some strings and perform some simple *rustling*. Let's use the famous poem *My Shadow* by the poet Robert Louis Stevenson as our input.

[PRE2]

The next step is to search the poem for occurrences of the pattern and print the results. To achieve this, we'll need to learn a bit about control flow.

# [Summary](#summary)

In this section, we:

*   Learned how to declare variables.
*   Explored Rust's type inference.

# [Next](#next)

Onward to control flow.

* * *

1.  [`let` statements](https://doc.rust-lang.org/reference/statements.html#let-statements) support more advanced features that are not being covered yet. [↩](#fr-1-1)

2.  In many cases, the compiler can infer the type allowing you to omit it. [↩](#fr-2-1)