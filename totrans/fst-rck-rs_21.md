# Borrowing

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/borrowing.html](https://freddiehaddad.github.io/fast-track-to-rust/borrowing.html)

Given the error in the previous section about borrowing a value after it has been moved, let's now focus on how to *borrow* a value.

## [References](#references)

Recall from the section on the [string slice `str`](types.html#string-slice-str) that we said it's usually seen in it's *borrowed* form `&str`. The `&` operator^([1](#footnote-1)) in the prefix position represents a borrow. In `find_matching_lines`, `pattern` is *borrowed*.

[PRE0]

## [Borrowing `lines`](#borrowing-lines)

In `find_matching_lines`, we can *borrow* `lines` by prefixing the parameter's type with an `&`, changing it to `&Vec<&str>`, and by prefixing the variable `lines` in `main` to `&lines`. After making these changes and re-running the program, we can see that it now works.

[PRE1]

## [Continuing to Refactor](#continuing-to-refactor)

Let's create another function to handle the creation of our intervals. Here is the function signature:

[PRE2]

This is the code that we'll transfer into the new function:

[PRE3]

Here is the revised code with the changes implemented. Review it and run the code.

[PRE4]

> Moving vs Borrowing
> 
> *   Why is it possible to *move* `match_lines` without causing an error?
> *   Considering heap allocations, what advantages might there be in moving `match_lines` instead of *borrowing* it?

# [Exercise](#exercise)

Develop a function named merge_intervals and transfer the specified code from main into this function, making any necessary updates. Construct another function called print_results and relocate the specified code from main into this function, updating it as needed.

*   Create a function named `merge_intervals` and move the specified code from `main` into this function, making any necessary updates.

    [PRE5]

*   Create another function called `print_results` and move the specified code from `main` into this function, updating it as needed.

    [PRE6]

*   Modify `main` to utilize these newly created functions.

> You can complete these exercises by updating the most recent version of the code provided above.

<details><summary>Solution</summary>

[PRE7]</details> 

# [Summary](#summary)

Although the concepts of ownership and borrowing are relatively straightforward, they can be frustrating when learning Rust. Reading through the official documentation on [Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) will certainly help overcome this challenge. Keep the following points in mind as you continue on your journey with Rust:

**Ownership Rules**

*   Each value in Rust has an owner.
*   There can only be one owner at a time.
*   When the owner goes out of scope, the value is dropped.

**Borrowing Rules**

*   At any given time, you can have either one mutable reference or any number of immutable references.
*   References must always be valid.

# [Next](#next)

With our new understanding of ownership and borrowing, let's switch our focus to error handling.

* * *

1.  The `&` operator can have different meanings depending on the context. For example, when used an infix operator, it becomes a bitwise AND. [↩](#fr-1-1)