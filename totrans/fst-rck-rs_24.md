# Cursor

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/cursor.html](https://freddiehaddad.github.io/fast-track-to-rust/cursor.html)

Our production rustle program now has the capability to access real files. However, the Rust Playground does not support opening files directly. To ensure this course remains functional in your web browser, we need to use an in-memory buffer to simulate a file. This technique of mocking an open file is also commonly used in unit testing, making it a valuable concept to explore.

The [`Cursor`](https://doc.rust-lang.org/std/io/struct.Cursor.html) ^([1](#footnote-1)) is used with in-memory buffers to provide [`Read`](https://doc.rust-lang.org/std/io/trait.Read.html) or [`Write`](https://doc.rust-lang.org/std/io/trait.Write.html) functionality. Without digressing too much, the `BufReader` we are using works on objects that implement the [`Read`](https://doc.rust-lang.org/std/io/trait.Read.html) trait. For now, think of a [trait](https://doc.rust-lang.org/book/ch10-02-traits.html) as an interface in object-oriented programming languages, with some differences.

## [Mocking a File with Cursor](#mocking-a-file-with-cursor)

We only need to make a few changes to our program to utilize `Cursor`. Let's start by updating the `read_file` function to accept any object that implements the `Read` trait as an argument.

[PRE0]

Next, we'll reintroduce our famous poem and use it as our in-memory buffer to represent our file.

[PRE1]

Finally, we comment out the lines that handled opening a file and calling `read_file`, and instead, we directly call `read_file` with `mock_file`.

[PRE2]

## [Putting it All Together](#putting-it-all-together)

With these changes applied to our rustle program, we can once again utilize the Rust Playground to extend its functionality and continue learning Rust.

[PRE3]

What? You don't believe me! Give it a whirl and see for yourself!

> Since we commented out the file handling code, some previously necessary imports are now unused. The `#![allow(unused_imports)]` attribute in Rust instructs the compiler to permit these unused imports without issuing warnings. We'll delve deeper into attributes when we discuss custom types and implement command line argument support.

# [Next](#next)

We're ready to add support for regular expressions for pattern matching. We'll take a brief detour to learn about project management in Rust, which will allow us to use packages (also known as crates) to add this functionality.

* * *

1.  A Cursor wraps an in-memory buffer and provides it with a [`Seek`](https://doc.rust-lang.org/std/io/trait.Seek.html) implementation. [↩](#fr-1-1)