# Multithreaded Rustle

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/multithreaded_rustle.html](https://freddiehaddad.github.io/fast-track-to-rust/multithreaded_rustle.html)

With our understanding of scoped vs non-scoped threads, we are now prepared to correctly update rustle to process each file specified on the command line in a separate thread.

Here's the updated version of the program with the changes visible.

[PRE0]

> Missing Error Output
> 
> [PRE1]
> 
> The error message for the bad file doesn't appear in the playground output because standard error output isn't captured.

Our rustle program is now multithreaded and processes all the input files in parallel! Let's walk through the code changes.

### [`mock_disk`](#mock_disk)

The `mock_disk` [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html) simulates disk access to check if a file exists and is accessible. The filename serves as the key, while the file's contents are the value. This approach aids in testing and development, but its use here is solely for Rust playground compatibility. To ensure the creation of multiple threads, I added a new poem written by `yours truly`.

### [`thread::scope`](#threadscope)

1.  Iterate over all files specified on the command line using the `map` iterator adapter, which returns a `Result`. The `Ok` variant holds the filename if valid, while the `Error` holds the error for an invalid filename.
2.  The `map_ok` iterator adapter processes each `Result`, calling the provided closure on any `Ok` values, allowing us to ignore any invalid filenames. The provided `Scope` (`s`) spawns one thread per file for processing. The closure returns a `Result`: `Err` with an error message in a `RustleFailure` struct if processing fails, or `Ok` with a `RustleSuccess` struct containing intervals and lines from the input file if successful.
3.  Use `collect` to create a vector (`Vec`) of results from each file iteration, binding it to `handles`.
4.  Finally, iterate over the elements in the `handles` vector using a for loop. Print any errors to standard error, and pass successful pattern matching results to the `print_results` function for output to standard output.

### [`find_matching_lines`](#find_matching_lines)

Since each thread needs access to the `regex` object, the value is borrowed instead of moved.

# [Summary](#summary)

*   Ownership and type systems are powerful tools for managing memory safety and concurrency issues. By leveraging ownership and type checking, many concurrency errors in Rust are caught at compile time rather than at runtime.
*   Unlike non-scoped threads, scoped threads can borrow non-`'static` data because the scope ensures all threads are joined before it ends.

# [Exercise](#exercise)

The fork/join model implemented is suboptimal because it waits for all threads to finish and join before printing any results. To address this, we can use the [`mpsc`](https://doc.rust-lang.org/std/sync/mpsc/index.html) (multiple producer, single consumer) module, which allows threads to send results to a central receiver as soon as they are ready. This enables the program to start outputting results immediately, enhancing its responsiveness and efficiency. Modify the program to make use of `mpsc`.

**HINT**: The final solution should have a structure similar to:

[PRE2]

[PRE3]

<details><summary>Solution</summary>

[PRE4]</details> 

# [Next](#next)

Wrapping things up!