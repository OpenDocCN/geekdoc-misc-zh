# Vec

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/vec.html](https://freddiehaddad.github.io/fast-track-to-rust/vec.html)

A `Vec`, short for vector, is a contiguous growable array type, written as `Vec<T>`. Although we haven't covered user-defined types yet, `Vec` is implemented using a `struct`.^([1](#footnote-1)) It supports many familiar operations like `push`, `pop`, and `len`, but also includes some operations you might not be familiar with.

## [Storing our Lines in a Vector](#storing-our-lines-in-a-vector)

Let's populate a vector with the input we've been using so far in our rustle program. There are several ways to create a vector, and the [documentation](https://doc.rust-lang.org/std/vec/struct.Vec.html) provides plenty of examples. We'll explore a few of them.

### [Using `push`](#using-push)

Someone with a C++ background might be inclined to achieve this using a variant of the following form:

> Hidden code
> 
> To make reading the code easier, only the new parts are visible. You can view previously seen code by clicking the *Show hidden lines* button when hovering over the code block.

[PRE0]

We haven't discussed traits yet, so for now, just know that `:?` specifies formatting the output with the `Debug`^([2](#footnote-2)) trait. The vector type implements the `fmt::Debug` trait.

### [Using an Iterator](#using-an-iterator)

While using `push` is functionally correct, it introduces a mutable variable unnecessarily. An idiomatic solution would look like this:

[PRE1]

> Favoring immutability
> 
> The concept of being *immutable by default* is one of the many ways Rust encourages you to write code that leverages its safety features and supports easy concurrency.

## [Tracking all Matches](#tracking-all-matches)

Now that we have a vector containing all the lines in our poem, let's create another vector to hold the line numbers where the pattern was found.

[PRE2]

Instead of using `from_iter`, you can also use `collect`.

> The inferred type (`_`) in `Vec<_>` *asks* the compiler to infer the type if possible based on the surrounding context.^([2](#footnote-2))

## [Creating Intervals from Matched Lines](#creating-intervals-from-matched-lines)

The `map` function invokes the `closure` once for each value in the vector, passing `line_no` (the line number) to the function. We use this to identify the lines before and after the match that we want to print. To handle potential out-of-bounds indexing, we use `saturating_add` and `saturating_sub`.

[PRE3]

## [Merging Intervals](#merging-intervals)

Merging overlapping intervals is straightforward because they are already sorted, and the ending value of the next interval must be greater than the current one. We could store the merged intervals in a new Vector, but that would be inefficient. Instead, we'll make our `intervals` vector mutable and take advantage of the `dedup_by` iterator adaptor to perform the merge.

[PRE4]

The [`dedup_by`](https://docs.rs/itertools/latest/itertools/trait.Itertools.html#method.dedup_by) iterator adaptor removes consecutive identical elements based on a provided closure. It starts by calling the closure with the first (`prev`) and second (`next`) elements in the collection. If the closure returns `false`, `prev` becomes `next`, `next` is advanced, and the closure is called with the new elements. If the closure returns `true`, only `next` is advanced. This behavior allows us to update `prev` to be the merged interval, enabling efficient merging of overlapping intervals.

> Tuple fields are accessed using a 0-based index, just like array elements.

## [Print the Results](#print-the-results)

With our intervals merged, we can now print out the results correctly!

[PRE5]

## [We Did It!](#we-did-it)

We have a working rustle program! Take some time to review everything we've covered so far. The rest of the course is going to move quickly.

# [Summary](#summary)

We covered quite a bit in this section:

*   `collect` converts any iterable into a collection.
*   `saturating_add` and `saturating_sub` prevent overflow.
*   `skip` creates an iterator that skips elements until `n` elements are skipped or the end of the iterator is reached, whichever comes first.
*   `take` creates an iterator that yields elements until `n` elements are yielded or the end of the iterator is reached, whichever comes first.
*   The `println!` macro supports the [`:?`](https://doc.rust-lang.org/std/fmt/index.html#fmtdisplay-vs-fmtdebug) format specifier, which is intended to help with debugging Rust code. All public types should implement the `fmt::Debug trait`.^([3](#footnote-3))

# [Next](#next)

Let's dive into the concepts of ownership and borrowing.

* * *

1.  Refer to the [`Vec` source code](https://doc.rust-lang.org/src/alloc/vec/mod.rs.html) see it's full implementation. The `struct` definition is on line [397](https://doc.rust-lang.org/src/alloc/vec/mod.rs.html#397). [↩](#fr-1-1)

2.  The [Inferred type](https://doc.rust-lang.org/reference/types/inferred.html?highlight=Vec%3C_%3E#inferred-type) is part of the type system in Rust. [↩](#fr-2-1) [↩2](#fr-2-2)

3.  Details about the `Debug` trait can be found [here](https://doc.rust-lang.org/std/fmt/trait.Debug.html). [↩](#fr-3-1)