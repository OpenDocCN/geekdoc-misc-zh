# Command Line Arguments

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/clap.html](https://freddiehaddad.github.io/fast-track-to-rust/clap.html)

In the [`Cargo.toml`](cargo_toml.html) section, you were asked to add the [`clap`](https://crates.io/crates/clap) crate as a dependency to support command line argument parsing for our rustle program. With our current understanding of attributes, it's an ideal time to utilize this crate by extending our rustle program to handle command line arguments.

One method for defining command line arguments with `clap` involves using custom attributes. This is why we specified the derive feature in the dependency.

If you didn't complete the exercise and are working through this course locally, you can add the dependency to the rustle crate with:

[PRE0]

## [Advanced Attributes](#advanced-attributes)

The topic of [macro attributes](https://doc.rust-lang.org/reference/procedural-macros.html#attribute-macros) and [derive macro helper attributes](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macro-helper-attributes) is quite advanced and beyond the scope of this course. Therefore, we won't delve into their inner workings in depth. However, keep this section in mind as you continue your Rust journey, because the time will likely come when you will need to implement similar attributes yourself for code generation.

## [Extending rustle](#extending-rustle)

We're going to add command line argument support to our program. However, we'll continue to mock the command line arguments to keep developing this course online. After configuring `clap`, this will be the auto-generated help (i.e., typing `rustle --help` in the terminal).

[PRE1]

> The `CLAP` documentation is very extensive and includes plenty of examples to learn from. If you find yourself building a CLI application, you will most certainly want to reference the [documentation](https://crates.io/crates/clap).

Here's the updated version of rustle with command line argument support added:

[PRE2]

# [Summary](#summary)

We made some minor code changes along with configuring `clap`. Most of it should be straightforward by now, so we'll focus on the new aspects:

*   The [`PathBuf`](https://doc.rust-lang.org/std/path/struct.PathBuf.html) module facilitates cross-platform path manipulation. Since our rustle program requires files to search, it's better to use `PathBuf` for handling that input.
*   We updated `print_results` to take a new boolean argument, `line_number`, which specifies whether or not to print line numbers in the output. If `true`, the `print!` macro is used to output the line number without emitting a newline.
*   We used `clap` attributes to derive our command line arguments. The `clap` [documentation](https://crates.io/crates/clap) covers these attributes in full detail.
*   In `main`, we mock command line arguments with an array of string slices that gets parsed by `clap`.

    > The `match` expression is for development purposes. If we made any mistakes in our mock command line arguments, we would catch the error and print it.

*   Since we defined the `before_context` and `after_context` variables as `u8` in the `Cli` structure but use `usize` throughout the code, an explicit cast using [`as`](https://doc.rust-lang.org/std/keyword.as.html) is necessary when assigning these values to local variables.

# [Next](#next)

Onward to concurrency!