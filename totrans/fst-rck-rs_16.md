# Closures

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/closures.html](https://freddiehaddad.github.io/fast-track-to-rust/closures.html)

In Rust, [closures](https://doc.rust-lang.org/book/ch13-01-closures.html) are functions that can capture their surrounding environment, clearly express the programmer's intent, and achieve this with low-level performance. They are quite common in functional programming languages.

Closures in Rust have some distinct characteristics:

*   Parameters are enclosed with `||` instead of `()`.
*   Curly braces `{}` around the function body are optional for single-line expressions.

## [Returning to our Loop](#returning-to-our-loop)

[PRE0]

In the code snippet, the closure is:

[PRE1]

## [`filter_map`](#filter_map)

The [`filter_map`](https://doc.rust-lang.org/std/iter/struct.FilterMap.html) ^([1](#footnote-1)) function creates an iterator that both filters and maps. It calls a closure and filters out the results that are `None`, leaving us with an iterator of tuples containing the line number and line for all matches of our pattern. When the `for` loop consumes the iterator, we only need to print the results, as we are left with only the lines that contained the pattern!

> Recall that `enumerate` returns an iterator of `tuple`s. `filter_map` receives the `tuple` as the argument to the closure.

# [Exercise](#exercise)

*   Replace `filter_map` with `map` and `filter` to achieve the same output. Notice how `filter_map` results in more efficient and concise code.

<details><summary>Solution</summary>

[PRE2]

> The underscore `_` prefix in `_line_no` is how we tell the Rust compiler that we are intentionally ignoring the first argument. Without it the compiler will complain.</details> 

# [Summary](#summary)

In this section we:

*   introduced the `Option` `enum`
*   learned about closures
*   worked with iterators
*   learned about the `mut` keyword

# [Next](#next)

Onward to collections!

* * *

1.  Separate `filter` and `map` iterators also exist. [↩](#fr-1-1)