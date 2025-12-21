# There Can Be Only One

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/there_can_be_only_one.html](https://freddiehaddad.github.io/fast-track-to-rust/there_can_be_only_one.html)

Currently, our entire rustle program is contained within the `main` function. This approach was chosen to address the challenges of teaching a course in a way that introduces important concepts logically and in an easily digestible manner. However, the time has come to refactor some of the code from the `main` function into separate functions.

Let's start by creating a function to handle the work of finding all the lines in the input that contain the specified pattern. Here is the function signature:

[PRE0]

This is the code that we'll transfer into the new function:

[PRE1]

Here is the revised code with the changes implemented. Review it and run the code.

[PRE2]

## [Uh-oh!](#uh-oh)

A minor code change caused an issue with the program. Fortunately, the Rust compiler offers helpful information for diagnosing the problem. However, if you're not familiar with Rust's ownership rules, understanding this error can be challenging. Let's break down the error and understand what went wrong. Here are the key details from the error message, cleaned up for readability:

[PRE3]

### [Unpacking the Error](#unpacking-the-error)

Copy trait, value moved, value borrowed. What the heck does all this mean?

#### [Copy Trait](#copy-trait)

We'll explore [traits](https://doc.rust-lang.org/book/ch10-02-traits.html) in more detail later in the course. For now, just know that when a type implements the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait, its values are duplicated when assigned to a new variable. This means that after an assignment, both the original and the new variable can be used independently.

The `lines` vector we passed to the `find_matching_lines` function does *not* implement the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait.

#### [Value Moved](#value-moved)

By default, variable bindings in Rust follow *move semantics*.^([1](#footnote-1)) When a value is *moved*, its ownership is transferred to the new variable, rendering the original variable invalid and unusable.

Since the `lines` vector does not implement the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait, its value was *moved*, rendering the original value in *main* invalid.

#### [Value Borrowed](#value-borrowed)

Because the `lines` variable in `main` becomes invalid due to the *move*, any attempt to [*borrow*](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html#references-and-borrowing) or reference its value is invalid. This is why the compiler generates the message "value borrowed here after move".

> Move Semantics
> 
> Rust's move semantics play an integral part in ensuring memory safety by detecting common memory-related errors, like null pointer dereferencing, buffer overflows, and use-after-free, during compile time, thereby preventing them from happening at runtime.

* * *

1.  There are some exceptions in Rust. For example, most primitive types implement the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait. [↩](#fr-1-1)