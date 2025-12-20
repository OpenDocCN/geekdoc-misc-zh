# match

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/02_match.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/02_match.html)

你可能会想知道——你实际上可以用枚举做什么？

最常见的操作是对其进行 **匹配**。

```rs
enum Status {
    ToDo,
    InProgress,
    Done
}

impl Status {
    fn is_done(&self) -> bool {
        match self {
            Status::Done => true,
            // The `|` operator lets you match multiple patterns.
            // It reads as "either `Status::ToDo` or `Status::InProgress`".
            Status::InProgress | Status::ToDo => false
        }
    }
}
```

一个 `match` 语句允许你将 Rust 值与一系列 **模式** 进行比较。

你可以将其视为类型级别的 `if`。如果 `status` 是 `Done` 变体，则执行第一个块；如果它是 `InProgress` 或 `ToDo` 变体，则执行第二个块。

## 详尽性

这里有一个关键细节：`match` 是 **详尽性** 的。你必须处理所有枚举变体。

如果你忘记处理一个变体，Rust 将在编译时通过错误阻止你。

例如，如果我们忘记处理 `ToDo` 变体：

```rs
match self {
    Status::Done => true,
    Status::InProgress => false,
}
```

编译器会抱怨：

```rs
error[E0004]: non-exhaustive patterns: `ToDo` not covered
 --> src/main.rs:5:9
  |
5 |     match status {
  |     ^^^^^^^^^^^^ pattern `ToDo` not covered 
```

这非常重要！

代码库会随着时间的推移而演变——你可能会在以后添加一个新的状态，例如 `Blocked`。Rust 编译器将为每个缺少对新变体逻辑处理的 `match` 语句发出错误。这就是为什么 Rust 开发者经常赞美“由编译器驱动的重构”——编译器告诉你下一步该做什么，你只需修复它报告的内容。

## 通配符

如果你不在乎一个或多个变体，你可以使用 `_` 模式作为一个通配符：

```rs
match status {
    Status::Done => true,
    _ => false
}
```

`_` 模式匹配任何之前模式未匹配的内容。

通过使用这个通配符模式，你 _ 不会 _ 获得由编译器驱动的重构的好处。如果你添加了一个新的枚举变体，编译器 _ 不会 _ 告诉你你没有处理它。

如果你注重正确性，避免使用通配符。利用编译器重新检查所有匹配点，并确定如何处理新的枚举变体。

## 练习

本节的练习位于 `05_ticket_v2/02_match` 中。
