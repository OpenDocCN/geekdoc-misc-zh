# thiserror

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/12_thiserror.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/12_thiserror.html)

这有点像是一个小插曲，不是吗？但这是必要的！

让我们回到正题：自定义错误类型和 `thiserror`。

## 自定义错误类型

我们已经看到了如何为自定义错误类型“手动”实现 `Error` 特性。

想象一下，你可能需要在代码库中的大多数错误类型上执行此操作。这岂不是很多样板代码，对吧？

我们可以通过使用 [thiserror](https://docs.rs/thiserror/latest/thiserror/) 来移除一些样板代码，这是一个提供 **过程宏** 以简化自定义错误类型创建的 Rust 包。

```rs
#[derive(thiserror::Error, Debug)]
enum TicketNewError {
    #[error("{0}")]
    TitleError(String),
    #[error("{0}")]
    DescriptionError(String),
}
```

## 你可以编写自己的宏

我们到目前为止看到的所有 `derive` 宏都是由 Rust 标准库提供的。

`thiserror::Error` 是第一个 **第三方** `derive` 宏的例子。

`derive` 宏是 **过程宏** 的一个子集，一种在编译时生成 Rust 代码的方法。我们不会在本课程中深入探讨如何编写过程宏的细节，但重要的是要知道你可以编写自己的宏！

这是一个在更高级的 Rust 课程中需要探讨的主题。

## 自定义语法

每个过程宏都可以定义自己的语法，这通常在包的文档中解释。对于 `thiserror` 来说，我们有：

+   `#[derive(thiserror::Error)]`: 这是使用 `thiserror` 为自定义错误类型推导 `Error` 特性的语法。

+   `#[error("{0}")]`: 这是为自定义错误类型的每个变体定义 `Display` 实现的语法。当错误显示时，`{0}` 被替换为变体的零索引字段（在这种情况下是 `String`）。

## 练习

本节练习位于 [05_ticket_v2/12_thiserror](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/12_thiserror)
