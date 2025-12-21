# 错误处理

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/error_handling.html`](https://freddiehaddad.github.io/fast-track-to-rust/error_handling.html)

许多程序使用异常等机制来处理错误，但 Rust 采用不同的方法。Rust 没有异常。相反，它使用 `Result` 类型来处理可恢复错误，并使用 `panic!` 宏来处理不可恢复错误。类似于我们之前讨论的 `Option` `enum`，`Result` 是另一个 `enum`。

## `Result<T, E>`

`Result<T, E>` 是用于返回和传播错误的类型。类似于 `Option`，它有两个变体：`Ok(T)`，表示成功并包含一个值，以及 `Err(E)`，表示错误并包含一个错误值。`T` 和 `E` 是我们将很快详细讨论的泛型类型参数。现在，重要的是要知道 `T` 代表在 `Ok` 变体中成功情况下返回的值的类型，而 `E` 代表在 `Err` 变体中失败情况下返回的错误类型。

```rs
enum Result<T, E> {
   Ok(T),
   Err(E),
}
```

## 附加资源

Rust 文档的几个部分详细介绍了 [错误处理](https://doc.rust-lang.org/book/ch09-00-error-handling.html)。

这里有一些有用的链接：

+   [使用 panic! 的不可恢复错误](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html)：有关如何调试引发 panic 的代码的有用信息。

+   [使用 Result 的可恢复错误](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)：深入探讨 `Result` 和通用错误处理。

+   [惊慌失措！还是不惊慌？](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)：关于在库代码中如何决定是否惊慌的通用指南。

+   [问号运算符](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator)：用于将错误传播到调用函数的有用工具.^(1)

* * *

1.  我们将在重构代码时介绍问号运算符 `?`。↩
