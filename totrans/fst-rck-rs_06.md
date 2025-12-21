# Package Creation

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/package_creation.html](https://freddiehaddad.github.io/fast-track-to-rust/package_creation.html)

Let's make sure all the prerequisites are in place. You should have followed the [installation](installation.html) instructions to prepare your development environment. After those steps are complete, you should be able to run the following commands:

[PRE0]

> The version numbers might be different, but the output should look relatively similar.

If the above commands worked, you're ready to go!

1.  Use `cargo new rustle` to create a new Rust package named `rustle` for our project:

    [PRE1]

2.  Navigate to the `rustle` directory and use `cargo run` to build and run the program:

    [PRE2]

3.  Explore some of the other actions you can perform with `cargo` using `cargo --help`.

    *   `cargo build` - compile the current package
    *   `cargo build --release` - build the project in release mode (with optimizations)
    *   `cargo check` - analyze the current package and report errors (no object files generated)
    *   `cargo test` - run unit tests
    *   and more...

# [Summary](#summary)

In this section, we:

*   Created a package.
*   Compiled and ran the boilerplate code.
*   Learned a bit about Cargo.

# [Next](#next)

Let's see what `cargo new` actually did!