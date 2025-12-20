# 索引

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/13_index.html`](https://rust-exercises.com/100-exercises/06_ticket_management/13_index.html)

`TicketStore::get` 返回一个针对给定 `TicketId` 的 `Option<&Ticket>`。

我们之前已经看到如何使用 Rust 的索引语法访问数组和向量的元素：

```rs
let v = vec![0, 1, 2];
assert_eq!(v[0], 0);
```

我们如何为 `TicketStore` 提供相同的体验？

你猜对了：我们需要实现一个特征，`Index`！

## 索引

`Index` 特征在 Rust 的标准库中定义：

```rs
// Slightly simplified
pub trait Index<Idx>
{
    type Output;

    // Required method
    fn index(&self, index: Idx) -> &Self::Output;
}
```

它具有：

+   一个泛型参数，`Idx`，用于表示索引类型

+   一个关联类型，`Output`，用于表示我们使用索引检索的类型

注意到 `index` 方法不返回 `Option`。假设是，如果你尝试访问不存在的元素，`index` 将会 panic，就像数组或 vec 索引那样。

## 练习

本节的练习位于 [06_ticket_management/13_index](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/13_index)
