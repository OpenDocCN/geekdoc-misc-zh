# Interval

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/interval.html](https://freddiehaddad.github.io/fast-track-to-rust/interval.html)

The current version of our `Interval` is limited to the `usize` type. If we want to support floating point values, negative integers, or other exotic numeric types, it won't work. We're going to address this by making it compatible with any numeric type, with some restrictions.^([1](#footnote-1))

## [Generic Data Type](#generic-data-type)

The current definition of our `Interval` `struct` specifies the field types as `usize`. To redefine the `struct` to use a generic type parameter for its fields, we use the `<>` syntax.

[PRE0]

> By using a single generic type to define `Interval<T>`, we indicate that the `Interval<T>` `struct` is generic over some type `T`, and the fields `start` and `end` are both of that same type, whatever it may be. If we attempt to create an instance of `Interval<T>` with fields of different types, our code won't compile. To support different types for the fields, we would need to specify additional generic types, such as `struct Interval<T, U>`.

You've probably guessed it already, but this code won't compile. Take a moment to think about why that might be, and then run the code to see what the compiler has to say.

[PRE1]

As you guessed it, there's a lot of compiler errors and they're very helpful!

*   [E0107](https://doc.rust-lang.org/stable/error_codes/E0107.html): missing generics for `struct` `Interval`

Let's walk through the errors one by one. The first error informs us that the return value on line 26 references a generic type but fails to specify one. It shows the definition of the type on line 141 and provides a helpful tip for how to correct it. The compiler suggests appending `<T>` to `Interval` and specifying the type for `T`, which in our case will be `usize`.

[PRE2]

The fix should be relatively straightforward to understand, as we've used the same approach for other generic types we've worked with. Let's apply the fix to all the functions and try again!

[PRE3]

As expected, we still have some more compiler errors to work through and these lead us into how we implement methods for a generic type!

[PRE4]

## [Inherent Implementation](#inherent-implementation)

There are two main types of implementation we define: inherent implementations (standalone) and trait implementations.^([2](#footnote-2)) We'll focus on inherent implementation first and explore trait implementations towards the end of this section.

We need to update our `impl` block to support generic type parameters for our generic type, and the syntax is as follows:

[PRE5]

Here are the necessary changes. Review them and run the program again.

[PRE6]

Well, that didn't work! Now we have two new compiler errors:

*   [E0369]: binary operation `<=` cannot be applied to type `T`
*   [E0507]: cannot move out of `self.start` which is behind a shared reference

That's okay, because these errors are a perfect segue into trait bounds!

## [Trait Bounds](#trait-bounds)

The compiler generated a few very helpful error messages, which we can categorize into two types, both of which suggest the use of trait bounds:

[PRE7]

With an introduction to trait bounds, everything will become clear. Let's begin with the first error. The compiler indicates that a comparison between two generic types is being attempted in the `new` function, and not all types support this capability. In other words, not all types implement the [`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html) trait, which is necessary for using comparison operators like `<=` and `>=`.

> For those with an object-oriented programming background, a trait can be thought of as similar to an interface.

[PRE8]

Since our `Interval` `struct` is generic over `T`, the types for `start` and `end` can be anything, including types that aren't comparable. Therefore, the compiler is instructing us to restrict `T` to any type that implements the [`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html) trait. In other words, we need to place a *bound* on `T`.

The next error requires us to revisit the topic of move semantics in Rust. Except for primitive types, most standard library types and those found in third-party crates do not implement the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait. In other words, they do not have *copy semantics*. Let's examine the function where the error occurs:

[PRE9]

The `merge` function borrows the values for `self` and `other`. If the two intervals overlap, a new interval is returned with the values copied into it. Since we have been using `usize`, a type that implements the `Copy` trait, this worked. To ensure it continues to work, we need to place another bound on `T`, limiting it to types that implement the `Copy` trait.

> The compiler also mentions the [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html) trait, which allows for explicit duplication of an object via the `clone` method. This means we could specify the trait bound as `Clone` instead of `Copy` and update the method to explicitly call `clone`.

With an understanding of trait bounds, let's examine how to impose these restrictions on our `Interval`. Does the program work now?

[PRE10]

Voila! And we now have a generic `Interval` module that can support any type implementing the `Copy` and `PartialOrd` traits!

# [Exercise](#exercise)

*   Modify the program to use the `Clone` trait instead of `Copy`.

<details><summary>Solution</summary>

[PRE11]</details> 

[PRE12]

# [Next](#next)

Let's dive deeper into traits!

* * *

1.  The restrictions we place on the supported types are known as [trait bounds](https://doc.rust-lang.org/reference/trait-bounds.html). [↩](#fr-1-1)

2.  For more information on `impl Trait` syntax, see the [Rust book](https://doc.rust-lang.org/book/ch10-02-traits.html#returning-types-that-implement-traits) [↩](#fr-2-1)