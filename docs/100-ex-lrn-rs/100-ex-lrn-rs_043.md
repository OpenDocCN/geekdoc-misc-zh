# 枚举

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/01_enum.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/01_enum.html)

基于你在上一章中编写的验证逻辑 in a previous chapter，票据的有效状态只有几个：`To-Do`、`InProgress` 和 `Done`。

如果我们查看 `Ticket` 结构体中的 `status` 字段或 `new` 方法中的 `status` 参数类型，这一点并不明显：

```rs
#[derive(Debug, PartialEq)]
pub struct Ticket {
    title: String,
    description: String,
    status: String,
}

impl Ticket {
    pub fn new(
        title: String, 
        description: String, 
        status: String
    ) -> Self {
        // [...]
    }
}
```

在这两种情况下，我们使用 `String` 来表示 `status` 字段。`String` 是一个非常通用的类型——它不会立即传达 `status` 字段具有有限的可能值的信 息。更糟糕的是，调用 `Ticket::new` 的用户只有在 **运行时** 才能知道他们提供的状态是否有效。

我们可以使用 **枚举** 来做得更好。

## `enum`（枚举）

枚举是一种可以具有一组固定值的类型，称为 **变体**。

在 Rust 中，你使用 `enum` 关键字来定义枚举：

```rs
enum Status {
    ToDo,
    InProgress,
    Done,
}
```

`enum`，就像 `struct` 一样，定义 **一个新的 Rust 类型**。

## 练习

本节练习位于 [`05_ticket_v2/01_enum`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/01_enum)
