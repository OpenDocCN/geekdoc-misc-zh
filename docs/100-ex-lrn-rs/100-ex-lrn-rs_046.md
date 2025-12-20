# 简洁的分支

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/04_if_let.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/04_if_let.html)

你之前练习的解决方案可能看起来像这样：

```rs
impl Ticket {
    pub fn assigned_to(&self) -> &str {
        match &self.status {
            Status::InProgress { assigned_to } => assigned_to,
            Status::Done | Status::ToDo => {
                panic!(
                    "Only `In-Progress` tickets can be \
                    assigned to someone"
                )
            }
        }
    }
}
```

你只关心 `Status::InProgress` 变体。你真的需要匹配所有其他变体吗？

新的构造函数来拯救！

## `if let`

`if let` 构造函数允许你匹配枚举的单个变体，而无需处理所有其他变体。

这就是你可以如何使用 `if let` 来简化 `assigned_to` 方法：

```rs
impl Ticket {
    pub fn assigned_to(&self) -> &str {
        if let Status::InProgress { assigned_to } = &self.status {
            assigned_to
        } else {
            panic!(
                "Only `In-Progress` tickets can be assigned to someone"
            );
        }
    }
}
```

## `let/else`

如果 `else` 分支旨在提前返回（恐慌也算作提前返回！），你可以使用 `let/else` 构造：

```rs
impl Ticket {
    pub fn assigned_to(&self) -> &str {
        let Status::InProgress { assigned_to } = &self.status else {
            panic!(
                "Only `In-Progress` tickets can be assigned to someone"
            );
        };
        assigned_to
    }
}
```

它允许你在不产生任何“右偏移”的情况下分配解构变量，即变量被分配在与它之前的代码相同的缩进级别上。

## 风格

`if let` 和 `let/else` 都是 Rust 的惯用构造。

根据你的需要使用它们来提高代码的可读性，但不要过度使用：当你需要时，`match` 总是存在的。

## 练习

本节的练习位于[`05_ticket_v2/04_if_let`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/04_if_let)
