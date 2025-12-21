# Control Flow

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/control_flow.html](https://freddiehaddad.github.io/fast-track-to-rust/control_flow.html)

Some of the common methods in Rust for controlling the flow of a program include:

*   [`if`](https://doc.rust-lang.org/reference/expressions/if-expr.html#if-expressions) and [`if let`](https://doc.rust-lang.org/reference/expressions/if-expr.html#if-let-expressions) expressions
*   [Loop expressions](https://doc.rust-lang.org/reference/expressions/loop-expr.html)
*   [`match` expressions](https://doc.rust-lang.org/reference/expressions/match-expr.html)

These methods help you manage the execution flow and make your code more efficient and readable.

We will use a `for` loop to iterate over all the lines in the poem, checking each for the substring specified by `pattern`. Each line will be evaluated using a `match` expression.

[PRE0]

## [`for` Loops](#for-loops)

The syntax of a `for` loop should look familiar. However, something interesting is happening on that line. Notice the method call `poem.lines()`. You might have thought poem was a string literal. How can it have methods? Well, as you guessed and as was mentioned earlier, string slices are more than just string literals. We'll explore them in more detail, so keep that in mind.

The purpose of the loop is quite clear: it iterates over each line in the poem.

## [`match` Expressions](#match-expressions)

You might have already figured it out, but the `match` expression is similar to an `if` expression in that it introduces a branch in the code execution. However, it has a very powerful feature: when used, the compiler ensures that all possible results of the [*scrutinee*](https://doc.rust-lang.org/reference/glossary.html#scrutinee) are covered. This aspect of [`match` expressions](https://doc.rust-lang.org/reference/expressions/match-expr.html) guarantees that all cases are handled.

Let's ensure we fully understand this. In the code snippet, comment out line 16 by prefixing it with `//`, and then run the code.

> Friendly compiler errors
> 
> Take a moment to appreciate just how helpful this compiler error is. The Rust compiler is truly your friend!

[PRE1]

The compiler error message is informing you that:

*   The `contains` method returns a boolean value.
*   The `false` case is not covered.
*   The Rust compiler can provide more information via `rustc --explain E0004`.

Let's see what the Rust compiler has to say:

[PRE2]

`match` arms have the following structure:

[PRE3]

## [`()` Unit Type](#-unit-type)

In situations where we don't want to perform any action, such as in the `false` arm, we can use the empty unit type `()`. We'll explore this more as we progress through the course.

# [Summary](#summary)

In this section, we:

*   Explored `for` loop expressions.
*   Examined `match` expressions.
*   Learned how the Rust compiler provides helpful error messages.
*   Were introduced to the empty unit type `()`.

# [Exercise](#exercise)

*   Replace the `match` expression with an [`if`](https://doc.rust-lang.org/reference/expressions/if-expr.html#if-expressions) expression.

<details><summary>Solution</summary>

[PRE4]</details> 

# [Next](#next)

Take a break if you need, and then let's continue!