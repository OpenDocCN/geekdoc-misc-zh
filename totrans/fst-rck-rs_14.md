# Iterators

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/iterators.html](https://freddiehaddad.github.io/fast-track-to-rust/iterators.html)

Iterators are pervasive in Rust, and delving into them in full detail would necessitate renaming this course to **Slow Track to Rust**. We'll cover the basics and direct you to the documentation for all the intricate details about [iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html#processing-a-series-of-items-with-iterators).

The [Control Flow](./control_flow.html) section explained that the call to `lines()` in the `for` loop returns an iterator. We say that the `for` loop *consumes* the iterator. However, in Rust, we can do much more than just consume iterators!

## [Iterator Adaptors](#iterator-adaptors)

New iterators can be created using [iterator adaptors](https://doc.rust-lang.org/book/ch13-02-iterators.html?search=#methods-that-produce-other-iterators). These adaptors generate new iterators that modify some aspect of the original. Let's use one to print line numbers.

The `enumerate` function creates an iterator that yields the current iteration count along with the value from the previous iterator, as tuples^([1](#footnote-1)) in the form `(index, value)`. In the loop, the type for `i` is `usize`, and the type for `line` is `&str`.

[PRE0]

## [Advanced Iterators](#advanced-iterators)

We can take it a step further by using the `filter_map` iterator adapter to return an iterator that includes only the items we want!

[PRE1]

Whoa! What just happened? We're on the fast track to learning Rust, so we're picking up the pace! Let's break this down because this code snippet needs some unpacking.

* * *

1.  A [tuple](https://doc.rust-lang.org/rust-by-example/primitives/tuples.html#tuples) is a collection of values of different types and is constructed using parentheses `()`. [↩](#fr-1-1)