# File I/O

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/file_io.html](https://freddiehaddad.github.io/fast-track-to-rust/file_io.html)

Our rustle program wouldn't be complete without the ability to search text files. Given the potential for I/O errors, adding this capability now is convenient as we explore error handling and the `Result` type. This also introduces us to additional packages in Rust's standard library.

> Up to this point, we've been able to use string literals in our rustle program because dynamic memory allocation wasn't needed. However, now that we will be reading from a file, dynamic memory allocation becomes necessary. The string slice is no longer sufficient, so we need to utilize the [`String`](https://doc.rust-lang.org/rust-by-example/std/str.html) ^([1](#footnote-1)) type in Rust.

> Storing Data on the Heap
> 
> Should you find yourself needing to allocate memory directly on the heap, the [`Box`](https://doc.rust-lang.org/std/boxed/struct.Box.html) type is commonly used. You can find numerous examples on its usage in the [documentation on the `Box` type](https://doc.rust-lang.org/book/ch15-01-box.html).

Let's start by creating a function that reads a file and returns a vector of strings (`Vec<String>`) where each string represents a line. Here is the function signature:^([2](#footnote-2)) ^([3](#footnote-3))

[PRE0]

This is the code that we'll add to the `read_file` function:

[PRE1]

The `read_file` function accepts a file handle and utilizes [`BufReader`](https://doc.rust-lang.org/std/io/struct.BufReader.html) to efficiently read the file line by line, storing each line in a vector of strings (`Vec<String>`), which it then returns to the caller.

> Many less efficient methods for reading a file and storing the results in a collection typically involve iterating over each line, converting it to a string, and then pushing the string into a vector. This approach requires intermediate memory allocations, which can become costly for large files. Additionally, each line read from the file potentially involves a system call. The [`BufReader`](https://doc.rust-lang.org/std/io/struct.BufReader.html) uses an internal buffer to read large chunks of data from the file, minimizing both memory allocations and system calls.

The modifications to the `main` function:

[PRE2]

## [Unpacking the Code](#unpacking-the-code)

There's a lot going on here, so let's break it down step by step.

### [`read_file`](#read_file)

[PRE3]

1.  **`BufReader`**: `BufReader::new(file)` creates a buffered reader from the provided `File`. This helps in efficiently reading the file line by line.

2.  **`lines()`**: The `lines()` method on `BufReader` returns an iterator over the lines in the file. Because reading from a file can file, each line is wrapped in a `Result`, which can be either `Ok` (containing the line) or `Err` (containing an error).

3.  **`map_while(Result::ok)`**: The `map_while` method is used to transform the iterator. It applies the `Result::ok` function to each item, which converts `Ok(line)` to `Some(line)` and `Err(_)` to `None`. The iteration stops when the first `None` is encountered. Here are the relevant parts from the [source code](https://doc.rust-lang.org/std/result/enum.Result.html), cleaned up for readability:

    [PRE4]

    This conversion is necessary because the map method requires the closure to return an `Option`. Converting `Err` to `None` drops the error value and causes `map_while` to stop yielding.

4.  **`collect()`**: The `collect()` method gathers all the `Some(line)` values into a `Vec<String>` that gets returned to the caller.

### [`main`](#main)

In the `main` function, we attempt to open a file, which can fail for various reasons. If the `Result` is `Ok`, we call `read_file` with the file value. Since we don't need the file handle afterward, borrowing isn't necessary. If an error occurs while opening the file, we use the `eprintln!` macro to print the error to standard error and then exit.

## [Putting it All Together](#putting-it-all-together)

Here are the changes with the unrelated parts of the program hidden:

[PRE5]

> Don't forget, you can reveal the hidden parts by clicking *Show hidden lines*.

# [Summary](#summary)

*   Rust requires acknowledging and handling errors before code compilation, ensuring robustness.
*   Errors are categorized into recoverable (e.g., file not found) and unrecoverable (e.g., out-of-bounds access).
*   Rust uses `Result<T, E>` for recoverable errors and `panic!` for unrecoverable errors, unlike other languages that use exceptions.

# [Next](#next)

To continue using the Rust Playground, opening an actual file isn't going to work. Let's see how we can leverage an in-memory buffer to represent an open file.

* * *

1.  Strings are implemented as `Vec<u8>` in Rust. Reference the [API](https://doc.rust-lang.org/stable/std/string/index.html) for details. [↩](#fr-1-1)

2.  Unfortunately, the Rust Playground doesn't support opening files, so you'll need to run this part of the code on your local machine. [↩](#fr-2-1)

3.  Rust offers several useful macros that are handy for developing and prototyping your program. [`todo!()`](https://doc.rust-lang.org/std/macro.todo.html) is one of them, and another is [`unimplemented!()`](https://doc.rust-lang.org/std/macro.unimplemented.html). [↩](#fr-3-1)