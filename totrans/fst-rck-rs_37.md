# Scope and Privacy

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/scope_and_privacy.html](https://freddiehaddad.github.io/fast-track-to-rust/scope_and_privacy.html)

We're going to convert all our `Interval` related code into a module. To define a module, we use the `mod` keyword followed by the module's name and enclose the body within curly braces.

[PRE0]

Here's the new version of our rustle program with the `Interval` related parts moved inside the `interval` module. In addition, comments have been added to the module which will be used to generate documentation in an upcoming section. Go ahead and run the code to see it in action!

[PRE1]

Uh-oh! Looks like we have all kinds of compiler errors! Among the chaos is two different errors having to do with scope and privacy.

*   [E0412](https://doc.rust-lang.org/stable/error_codes/E0412.html): cannot find type `Interval` in this scope
*   [E0433](https://doc.rust-lang.org/stable/error_codes/E0433.html): failed to resolve: use of undeclared type `Interval`

> Remember you can always use `rustc --explain EXXXX` which provides a detailed explanation of an error message.

## [Scope](#scope)

The first error indicates that the `Interval` type is not in scope. This is because it is now part of the `interval` module. To access it, we can use the full path name `interval::Interval` or create a shortcut with `use`. Since we don't want to replace every occurrence of `Interval` in our code with `interval::Interval`, we'll take advantage of `use`. Additionally, we need access to `IntervalError`, so we'll bring that into scope at the same time. When bringing multiple types into scope, we can wrap them in `{}` and separate them with `,`.

With that change in place, run the code again.

[PRE2]

Bugger! More compiler errors!

## [Privacy](#privacy)

Before we defined the `interval` module, all the types and their methods were public. However, once we enclosed everything in a module, they became private! By default, code within a module is private from its parent modules. To make a module public, we need to declare it with `pub mod` instead of just `mod`. Let's add the `pub` prefix and run the program again.

[PRE3]

More compiler errors! Who would have thought creating a module could be this complicated? The reason for this series of errors is to help us understand module scope and privacy. The emerging pattern is that modules default everything to private. Simply declaring the module public isn't enough; every type and method within the module must also be explicitly declared public if that is the intended design. So, let's prefix the methods and types with `pub` and hopefully achieve a successful compile!

[PRE4]

Alright, last time, I promise! As a final note on privacy, and as the compiler error pointed out, even the fields of a `struct` are private by default. So, the last step is to make the fields public. Let's do that and finally achieve a successful compile. Fingers crossed!

[PRE5]

Finally, the code compiles! Now, you might be wondering why we didn't have to declare the `enum` variants as public. If you are, good catch! The reason is that there are two exceptions to Rust's *everything is private*^([1](#footnote-1)) behavior:

1.  Associated items in a `pub` Trait are public by default.
2.  `enum` variants in a `pub enum` are public by default.

# [Summary](#summary)

This section focused heavily on emphasizing Rust's *everything is private* default behavior when it comes to modules. As you develop software, use privacy to your advantage and carefully decide what parts of the API should be made public.

Rust goes into great detail with regard to project management. As you create your own modules and crates, reviewing the section on [Managing Growing Projects with Packages, Crates, and Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) will be extremely valuable.

# [Exercises](#exercises)

> These exercises must be completed locally.

*   Move the `interval` module out of `main.rs` and into a separate file. Explore two approaches:
    1.  First, create a file `interval.rs` in the `src` directory.
    2.  Next, create a directory under `src` called `interval` and move `interval.rs` inside.
*   **Advanced**: Creating an external crate
    1.  Create a library crate `cargo new --lib interval` and move the interval code into it.
    2.  If you haven't already, create a binary crate `cargo new rustle` and update the `Cargo.toml` file to use the external crate from the previous step. Refer to the section on [Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) in [The Cargo Book](https://doc.rust-lang.org/cargo/) for guidance.

# [Next](#next)

Now, let's dive into generic types and make our `Interval` generic!

* * *

1.  Refer to the [Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) reference for details. [↩](#fr-1-1)