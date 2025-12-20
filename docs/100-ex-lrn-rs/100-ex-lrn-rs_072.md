# 可变索引

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/14_index_mut.html`](https://rust-exercises.com/100-exercises/06_ticket_management/14_index_mut.html)

`Index`允许只读访问。它不允许你修改你检索到的值。

## `IndexMut`（IndexMut）

如果你想允许可变性，你需要实现`IndexMut`特质。

```rs
// Slightly simplified
pub trait IndexMut<Idx>: Index<Idx>
{
    // Required method
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
```

只有当类型已经实现了`Index`时，才能实现`IndexMut`，因为它解锁了*额外*的能力。

## 练习
