# 所有权

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/ownership.html`](https://freddiehaddad.github.io/fast-track-to-rust/ownership.html)

所有权和借用是 Rust 的基本原则，它们确保了内存安全，无需垃圾回收器。所有权决定了内存的管理方式，而借用允许你引用数据而不获取所有权。理解这些概念对于编写高效且安全的 Rust 程序至关重要。

Rust 的文档在 [理解所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) 中对这些主题进行了深入探讨，强烈建议花些时间阅读这些材料。现在，让我们专注于所有权的核心原则。

## 核心原则

在我们继续课程的过程中，请记住这些关于所有权的规则：

+   Rust 中的每个值都有一个所有者。

+   一次只能有一个所有者。

+   当所有者超出作用域时，值将被*丢弃*。¹

* * *

1.  术语*丢弃*意味着内存被释放，对象的生存期结束。↩
