# 可见性

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/04_visibility.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/04_visibility.html)

当你开始将代码分解成多个模块时，你需要开始考虑 **可见性**。可见性决定了你的代码（或他人的代码）中哪些区域可以访问给定的实体，无论是结构体、函数、字段等。

## 默认为私有

默认情况下，Rust 中的一切都是 **私有的**。

私有实体只能被以下方式访问：

1.  在定义它的同一模块内，或者

1.  由其子模块之一

我们在之前的练习中广泛使用了它：

+   `create_todo_ticket` 工作正常（一旦添加了 `use` 语句），因为 `helpers` 是 crate 根的子模块，其中定义了 `Ticket`。因此，即使 `Ticket` 是私有的，`create_todo_ticket` 也可以无问题地访问 `Ticket`。

+   我们的所有单元测试都定义在它们所测试的代码的子模块中，因此它们可以无限制地访问一切。

## 可见性修饰符

你可以使用 **可见性修饰符** 修改实体的默认可见性。

一些常见的可见性修饰符包括：

+   `pub`: 使得实体 **公开**，即可以从定义它的模块外部访问，可能来自其他 crate。

+   `pub(crate)`: 使得实体在相同的 **crate** 内部公开，但不在其外部。

+   `pub(super)`: 使得实体在父模块内公开。

+   `pub(in path::to::module)`: 使得实体在指定的模块内公开。

你可以在模块、结构体、函数、字段等上使用这些修饰符。例如：

```rs
pub struct Configuration {
    pub(crate) version: u32,
    active: bool,
}
```

`Configuration` 是公开的，但你只能从同一 crate 内部访问 `version` 字段。相反，`active` 字段是私有的，只能从同一模块或其子模块内部访问。

## 练习

本节的练习位于 [`03_ticket_v1/04_visibility`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/04_visibility)
