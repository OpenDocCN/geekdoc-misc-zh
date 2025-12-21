# Regular Expressions

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/regular_expression.html](https://freddiehaddad.github.io/fast-track-to-rust/regular_expression.html)

With the `Regex` crate added to our project, we'll replace the `pattern` string slice we've been using with a regular expression.

## [Using Regex](#using-regex)

The `Regex` modules defines a `new` method that takes a regular expression, attempts to compile it, and returns a `Regex` object.^([1](#footnote-1))

[PRE0]

Since compiling a regular expression can fail (e.g., due to an invalid pattern), `new` returns a `Result`. Here is the function signature for `new`^([2](#footnote-2)):

[PRE1]

The function signature indicates that the `Ok` variant returns a `Regex`, while the `Err` variant returns an `Error`. Since our rustle program can't continue with an invalid regular expression, we need to catch that case, display a helpful error message, and exit the program.

Let's put all this together:

[PRE2]

Run the code to see the error. Then, correct the it by adding the missing parenthesis `)` and re-run the code.

## [Updating Rustle](#updating-rustle)

We now have enough context to modify our rustle program to include regular expression support. Below are the changes, with the unrelated parts of the program hidden:

[PRE3]

> Don't forget, you can reveal the hidden parts by clicking *Show hidden lines*.

The `let regex = match Regex::new(pattern)` variable binding expression might seem a bit unusual. The pattern is discussed in the Rust documentation section on [Recoverable Errors with Result](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html#recoverable-errors-with-result). To briefly explain: When the result is `Ok`, this code extracts the inner `re` value from the `Ok` variant and moves it to the variable `regex`.

# [Next](#next)

Onward to creating our own module!

* * *

1.  The `Regex` crate includes excellent [documentation](https://docs.rs/regex/latest/regex/) and detailed [examples](https://docs.rs/regex/latest/regex/#examples) to learn from. [↩](#fr-1-1)

2.  The source code for `new` can be found [here](https://docs.rs/regex/latest/src/regex/regex/string.rs.html#180-182). [↩](#fr-2-1)