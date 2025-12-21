# 自定义类型

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/custom_types.html`](https://freddiehaddad.github.io/fast-track-to-rust/custom_types.html)

Rust 提供了两种创建自定义类型的方法：`enum`（[枚举](https://doc.rust-lang.org/reference/items/enumerations.html)）和`struct`（[结构体](https://doc.rust-lang.org/reference/items/structs.html)）。它们之间的关键区别在于枚举有一个固定的变体集合，这意味着它们用于指示一个值是特定集合中可能值之一。另一方面，`struct`（[结构体](https://doc.rust-lang.org/reference/items/structs.html)）不限于一组可能的值。结构体允许将相关的值打包成有意义的组。

> 当我们查看`Option`和`Result`时，我们已经遇到了枚举。

在我们当前的 rustle 程序中，我们使用元组来表示区间。在本节中，我们将使用`struct`（[结构体](https://doc.rust-lang.org/reference/items/structs.html)）来替换元组，并为其添加各种操作的方法来增强它。最后，我们将定义一个`enum`（[枚举](https://doc.rust-lang.org/reference/items/enumerations.html)）来表示在创建和交互区间时可能出现的错误值。
