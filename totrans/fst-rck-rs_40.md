# Traits

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/traits.html](https://freddiehaddad.github.io/fast-track-to-rust/traits.html)

In the previous section, we specified trait bounds to restrict the types that can be used with our `Interval`. Let's formalize what a trait is:

A trait is officially defined as a collection of methods for an unknown type: `Self`.^([1](#footnote-1))

In simpler terms, a trait allows you to define shared behavior in an abstract way. It specifies a set of methods that a type must implement, similar to interfaces in other programming languages.

The [Rust By Example](https://doc.rust-lang.org/rust-by-example/) book includes many examples of [traits](https://doc.rust-lang.org/rust-by-example/trait.html) and explores their usage in depth. Reviewing this material is highly recommended.

> The compiler can automatically provide basic implementations for certain traits using the derive (`#[derive]`) [attribute](https://doc.rust-lang.org/reference/attributes.html). However, if more complex behavior is needed, these traits can still be manually implemented. Here is a list of derivable traits:

*   Comparison traits: [`Eq`](https://doc.rust-lang.org/std/cmp/trait.Eq.html), [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html), Ord, [`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html).
*   [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html), to create `T` from `&T` via a copy.
*   [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html), to give a type *copy semantics* instead of *move semantics*.
*   [`Hash`](https://doc.rust-lang.org/std/hash/trait.Hash.html), to compute a hash from `&T`.
*   [`Default`](https://doc.rust-lang.org/std/default/trait.Default.html), to create an empty instance of a data type.
*   [`Debug`](https://doc.rust-lang.org/std/fmt/trait.Debug.html), to format a value using the `{:?}` formatter.

## [Deriving a Trait](#deriving-a-trait)

Someone using our `Interval` might find it helpful to have an easy way to compare them. For instance, a user may want to check if two intervals are equal. The [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) trait, part of the [`cmp`](https://doc.rust-lang.org/std/cmp/index.html) module, specifies two methods that any type must define to implement the `PartialEq` trait.

[PRE0]

> Notice the comment above the `ne` method that says "Provided method." This indicates that if we manually implement this trait, we only need to provide an implementation for `eq`.

Here's our revised `Interval` with support for `PartialEq`, thanks to the derive attribute and the Rust compiler. Give it a try!

> The `Debug` trait has also been derived, enabling intervals to be printed in a programmer-facing context using the `:?` operator. This common pattern in Rust provides more helpful output in the program below.

[PRE1]

> The [`unwrap()`](https://doc.rust-lang.org/std/result/enum.Result.html#method.unwrap) method is implemented by `Result` and other types like `Option`. For `Result`, it returns the `Ok` value or panics if the value is `Err`. Its usage is generally discouraged and is only used here for brevity.

> Operator Overloading
> 
> You might have noticed the comparison between intervals using `==` and `!=`. This works because Rust includes support for operator overloading! You can find all the detailed information in the [Operator Overloading](https://doc.rust-lang.org/rust-by-example/trait/ops.html) section of the [Rust by Example](https://doc.rust-lang.org/rust-by-example/) book and in the [`ops`](https://doc.rust-lang.org/std/ops/index.html) module.

## [Implementing a Trait](#implementing-a-trait)

Just as comparing traits for equality can be helpful, so can generating a user-facing representation of an `Interval`. By implementing the [`Display`](https://doc.rust-lang.org/std/fmt/trait.Display.html) trait, we can achieve this quite efficiently. Additionally, implementing the `Display` trait automatically implements the [`ToString`](https://doc.rust-lang.org/std/string/trait.ToString.html) trait, enabling the use of the `to_string()` method. Let's enhance our `Interval` code to print an interval in the form `[x, y]`.

Here's the trait definition for `Display`:

[PRE2]

> The `<'_>` suffix next to `Formatter` is known as *lifetime annotation syntax*.^([2](#footnote-2))

Here's our revised `Interval` with the `Display` trait implemented. Give it a try!

[PRE3]

# [Summary](#summary)

*   Our interval module has been enhanced to support several new capabilities.
*   We can print programmer-facing intervals using the `Debug` trait and user-facing intervals using the `Display` trait.
*   We have limited support for comparing intervals through the `PartialEq` and `PartialOrd` traits.
*   A trait defines shared behavior abstractly, specifying methods a type must implement, similar to interfaces in other languages.
*   The compiler can automatically provide basic implementations for certain traits using the `#[derive]` attribute.
*   Rust includes support for operator overloading.

# [Exercise](#exercise)

*   Implement the [`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html) trait for `Interval`. To keep the code simple, you can return `None` for overlapping intervals.

[PRE4]

<details><summary>Solution</summary>

[PRE5]</details> 

# [Next](#next)

Now that we've covered traits, let's ensure our projects are synchronized before we proceed to exploring attributes.

Here's the completed code:

[PRE6]

* * *

1.  https://doc.rust-lang.org/rust-by-example/trait.html [↩](#fr-1-1)

2.  This is a separate topic that you can learn more about in the [Validating References with Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) section of the [Rust Programming Language](https://doc.rust-lang.org/stable/book/) and the [Lifetimes](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) section of [Rust By Example](https://doc.rust-lang.org/rust-by-example/). [↩](#fr-2-1)