# Enum

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/enum.html](https://freddiehaddad.github.io/fast-track-to-rust/enum.html)

An *[enumeration](https://doc.rust-lang.org/reference/items/enumerations.html)*, commonly known as an *[enum](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html)*, is declared using the keyword `enum`. Compared to other languges, enums in Rust offer greater flexibility and power. For instance, they support generics (as seen with the `Option` `enum`) and can encapsulate values within their variants! ^([1](#footnote-1))

## [Using an `enum` for Errors](#using-an-enum-for-errors)

For our rustle program, we'll create an `enum` to represent possible errors during `Interval` operations. For example, when a user creates an `Interval`, the starting value must be less than or equal to the ending value. Additionally, if a user wants to merge two intervals, they must overlap. If these conditions aren't met, we'll return an error (`Err`) using one of our `enum` variants.

## [Defining an `enum`](#defining-an-enum)

Below is the `IntervalError` `enum`, which lists the errors that we may need to return:

[PRE0]

## [Updating our Interval](#updating-our-interval)

First, we'll change the return type for the function `new` and the method `merge` to a `Result` with the `Ok` variant being an `Interval` and the `Err` variant the appropriate `IntervalError`:

[PRE1]

[PRE2]

> Observe how an `Interval` is created in `new` as opposed to `merge`. Since the parameter names in new precisely match the fields in the `Interval` `struct` definition, you can omit the field specifiers. This technique is referred to as *field init shorthand* syntax. ^([2](#footnote-2))

## [Updating Rustle](#updating-rustle)

With the `Interval` changes implemented, we need to update the `create_intervals` and `merge_intervals` functions to accommodate the `Result` return type.

[PRE3]

In `create_intervals`, the only change was the return type, which changed from `Vec<Interval>` to `Result<Vec<Interval>, IntervalError>`. You might wonder why this works. The concise answer is that the `Result` type implements the [`FromIterator`](https://doc.rust-lang.org/std/iter/trait.FromIterator.html) trait.

Imagine an intermediary collection of `Result` values created from calls to `Interval::new(start, end)`. The `FromIterator` trait implementation allows an iterator over `Result` values to be collected *into* a `Result` containing a collection of the underlying values or an `Err`. ^([3](#footnote-3)) In other words, the value contained in the `Result` returned by `Interval::new(start, end)` is stored in the `Vec<Interval>` collection which is then wrapped in a `Result`.

> We'll be exploring traits in the next section.

[PRE4]

In `merge_intervals`, the only change required is to the closure used in `coalesce`. We attempt to merge two intervals and invoke the [`or`](https://doc.rust-lang.org/std/result/enum.Result.html#method.or) method of `Result`. If the merge is successful, returning `Ok`, the value is passed back to `coalesce`. Otherwise, the `Err((p, c))` value provided to `or` is returned.

> `Result` methods like `map_err`, `or`, and `or_else` are often used in error handling because they allow benign errors to be managed while letting successful results pass through. Since the `merge` method only merges overlapping intervals, we replace the `Err` variant it returns with the tuple `(p, c)` needed by `coalesce`.

> Eager vs Lazy Evaluation
> 
> Depending on the use case, different `Result` methods may be more efficient. It's important to read the documentation to determine the best choice. For example, arguments passed to [`or`](https://doc.rust-lang.org/std/result/enum.Result.html#method.or) are eagerly evaluated. If you're passing the result of a function call, it's better to use [`or_else`](https://doc.rust-lang.org/std/result/enum.Result.html#method.or_else), which is lazily evaluated.

The final change required is in `main`. Since `create_intervals` now returns a `Result`, we use a `match` expression to check if the operation was successful. In the case of an `Err`, since it's unrecoverable, we print an error message and exit.

[PRE5]

# [Updating Rustle](#updating-rustle-1)

With our changes in place, our Interval now supports error handling via `Result` and our rustle program properly handles any errors.

[PRE6]

# [Summary](#summary)

The decision to use the [`Result`](https://doc.rust-lang.org/std/result/enum.Result.html) type for error handling in Rust provides a robust and flexible way of managing errors such as:

1.  **Explicit Error Handling**: Using `Result` makes error handling explicit. Functions that can fail return a `Result`, which forces the caller to handle the potential error, making the code more reliable and less prone to unexpected failures.
2.  **Recoverable Errors**: The `Result` type allows for recoverable errors. By returning a `Result`, the function gives the caller the option to handle the error in a way that makes sense for their specific context, rather than immediately terminating the program.
3.  **Type Safety**: Rust's type system ensures that errors are handled correctly. The `Result` type is part of this system, helping to prevent common errors like null pointer dereferencing and making the code safer and more predictable.
4.  **Composability**: The `Result` type implements traits like `FromIterator`, which allows for powerful and flexible error handling patterns. This makes it easier to work with collections of results and to propagate errors through multiple layers of function calls.

Overall, the use of `Result` aligns with Rust's goals of safety, concurrency, and performance, providing a clear and structured way to handle errors.

# [Exercise](#exercise)

*   Replace `Result::or` with `Result::map_err` in `merge_intervals`.

    <details><summary>Solution</summary>

    [PRE7]</details> 

[PRE8]

# [Next](#next)

With our Interval complete, let's make it a module!

* * *

1.  Refer to the documentation on [enum values](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html#enum-values). [↩](#fr-1-1)

2.  Refer to the documentation on *[field init shorthand](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-the-field-init-shorthand)* syntax. [↩](#fr-2-1)

3.  Refer to the documentation on [Collecting into a `Result`](https://doc.rust-lang.org/std/result/#collecting-into-result) for detailed explanation. [↩](#fr-3-1)