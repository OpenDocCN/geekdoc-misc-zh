# Struct

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/struct.html](https://freddiehaddad.github.io/fast-track-to-rust/struct.html)

We're going to create a type to represent an interval. Rust follows a standardized naming convention for types, where structures use `UpperCamelCase`^([1](#footnote-1)) for "type-level" constructs. Therefore, we'll name our `struct` `Interval`.

## [Defining our Struct](#defining-our-struct)

Our closed interval is going to represent the start and end of the lines to print:

[PRE0]

## [Defining Behavior](#defining-behavior)

Functions and methods are added by defining them inside an `impl` block:

[PRE1]

## [The `new` Function](#the-new-function)

As it is common convention in Rust to define a function called `new` for creating an object, we'll begin by defining one to return an `Interval`.

[PRE2]

> The keyword `Self`
> 
> The `Self` keywords in the return type and the body of the function are aliases for the type specified after the `impl` keyword, which in this case is `Interval`. While the type can be explicitly stated, the common convention is to use `Self`.

> Exclusion of the `return` keyword and (`;`)
> 
> The `return` keyword is unnecessary when the returned value is the final expression in a function. In this scenario, the semicolon (`;`) is omitted. ^([2](#footnote-2))

## [Methods](#methods)

Recall from our rustle program that we merged overlapping intervals to prevent printing the same line multiple times. It would be useful to create a method to check if two intervals overlap and another method to merge overlapping intervals. Let's outline these methods!

[PRE3]

> The `todo!()` and `unimplemented!()` macros can be useful if you are prototyping and just want a placeholder to let your code pass type analysis.

### [The `self` Method Receiver](#the-self-method-receiver)

You're probably accustomed to using the implicit `this` pointer (a hidden first parameter) in your class methods. In Rust, the [`self`](https://doc.rust-lang.org/std/keyword.self.html) keyword is used to represent the receiver of a method and the convention is to omit the type for this parameter. Depending on the intended behavior, it can be specified as `self`, `&self` or `&mut self`.^([3](#footnote-3))

> Omitting the type after `self` is syntactic sugar. It's short for `self: Self`. As `Self` is an alias to the actual type, the full expansion would be `self: Interval`, `self: &Interval` or `self: &mut Interval`.

## [Implementing the Methods](#implementing-the-methods)

Remember that our rustle program processes lines sequentially. This allows us to optimize the detection of overlapping intervals. However, this approach limits the versatility of our `Interval` type. As an exercise, you can work on making it more generic.

### [`overlaps`](#overlaps)

The `overlaps` method is fairly straightforward. We check if the `end` of the first interval is greater than or equal to the `start` of the next interval. The only caveat is the order of the comparison.

[PRE4]

### [`merge`](#merge)

The `merge` method returns a new `Interval` using the `start` of the first interval and the `end` of the second. The same caveat applies: the receiver must be the interval that comes first in the sequence.

In both cases, an immutable borrow for both intervals is sufficient since we do not need to mutate either value.

[PRE5]

### [Implementing `merge_intervals`](#implementing-merge_intervals)

Rust programmers coming from a C++ background might be inclined to implement this function using some variation of the following algorithm:

[PRE6]

While functionally correct, Rust features powerful crates that can make implementing this behavior more concise. One such crate is [`Itertools`](https://docs.rs/itertools/latest/itertools), which provides extra iterator adaptors. To use this crate, specify it as a dependency in `Crates.toml` and include it in `main.rs` with `use itertools::Itertools`. Let's see how the [`coalesce`](https://docs.rs/itertools/latest/itertools/trait.Itertools.html#method.coalesce) adaptor can simplify the code:

[PRE7]

> `into_iter`
> 
> In both implementations, we use `into_iter`, which creates a consuming iterator that moves each value out of the vector from start to end. This is another example of how we can take advantage of move semantics.
> 
> NOTE: Because the iterator consumes the data, the vector cannot be used afterward.

## [Updating Rustle](#updating-rustle)

It's time to update our rustle program to utilize our new type. Additionally, a few minor changes have been made to enhance the design, demonstrate some additional language features, and leverage move semantics. Give the program a run!

[PRE8]

## [Summarizing the Changes](#summarizing-the-changes)

Our rustle program now makes use of our custom type and includes a few other enhancements.

Let's review the changes:

`create_intervals` was updated with the following changes:

*   The return type was changed to `Vec<Interval>`
*   The tuple created from `start` and `end` are now used to create an `Interval`

`merge_intervals` was updated with the following changes:

*   The argument `intervals` now has a type of `Vec<Interval>` and is *moved* instead of the mutable borrow
*   `dedup_by` was replaced with `coalesce`

`print_results` was updated with the following changes:

*   The argument `intervals` is now a `Vec<Interval>`
*   The `take` and `skip` iterator adaptors were updated to use the fields from the `Interval`

> Each interval is *dropped* at the end of the loop iteration when written as `for interval in intervals`. If the loop were written as `for interval in &intervals`, we would *borrow* each value. The same applies if we had written the loop as `for interval in intervals.iter()`. The former is syntactic sugar for the latter.^([4](#footnote-4))

* * *

1.  Casing conforms to [RFC 430](https://github.com/rust-lang/rfcs/blob/master/text/0430-finalizing-naming-conventions.md) (C-CASE). [↩](#fr-1-1)

2.  Exclusion of `return` is discussed [here](https://doc.rust-lang.org/std/keyword.return.html). [↩](#fr-2-1)

3.  Method syntax is covered in full detail [here](https://doc.rust-lang.org/book/ch05-03-method-syntax.html). [↩](#fr-3-1)

4.  Details about consuming collections with `for in` and `into_iter` can be found [here](https://doc.rust-lang.org/rust-by-example/flow_control/for.html). [↩](#fr-4-1)