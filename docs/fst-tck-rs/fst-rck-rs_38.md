# 泛型类型

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/generic_types.html`](https://freddiehaddad.github.io/fast-track-to-rust/generic_types.html)

许多编程语言都包括有效处理概念重复的工具，Rust 也不例外。Rust 为泛型提供了强大的支持，这个话题几乎可以写成一整本书。然而，由于我们正在快速学习 Rust，我们将通过将上一节中的`interval`模块泛型化，来关注泛型和特质的核心理念。

> 在本课程中，我们已经开始使用泛型，例如`Vec<T>`、`Option<T>`和`Result<T, E>`。

与上一节中的方法类似，我们在努力使`interval`模块通用化的过程中，将检查这些有用的编译器错误。让你接触这些编译器错误的理由是为了说明编译器在处理语言时是多么有益。

让我们开始吧！
