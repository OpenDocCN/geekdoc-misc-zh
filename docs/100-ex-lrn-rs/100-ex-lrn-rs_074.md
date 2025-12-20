# 排序

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/16_btreemap.html`](https://rust-exercises.com/100-exercises/06_ticket_management/16_btreemap.html)

通过从 `Vec` 移动到 `HashMap`，我们提高了我们的票务管理系统性能，并在过程中简化了代码。

然而，并非一切尽善尽美。当遍历由 `Vec` 支持的存储时，我们可以确信票将按添加的顺序返回。

对于 `HashMap` 来说并非如此：你可以遍历票，但顺序是随机的。

通过从 `HashMap` 切换到 `BTreeMap`，我们可以恢复一致排序。

## `BTreeMap`

`BTreeMap` 保证条目按其键排序。

当你需要按特定顺序遍历条目或执行范围查询（例如，“给我所有 ID 在 10 到 20 之间的票”）时，这很有用。

就像 `HashMap` 一样，你不会在 `BTreeMap` 的定义中找到特征界限。但你会找到其方法上的特征界限。让我们看看 `insert`：

```rs
// `K` and `V` stand for the key and value types, respectively,
// just like in `HashMap`.
impl<K, V> BTreeMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        // implementation
    }
}
```

不再需要 `Hash`。相反，键类型必须实现 `Ord` 特征。

## `Ord`

`Ord` 特征用于比较值。

虽然 `PartialEq` 用于比较相等性，但 `Ord` 用于比较排序。

它在 `std::cmp` 中定义：

```rs
pub trait Ord: Eq + PartialOrd {
    fn cmp(&self, other: &Self) -> Ordering;
}
```

`cmp` 方法返回一个 `Ordering` 枚举，可以是 `Less`、`Equal` 或 `Greater` 之一。

`Ord` 需要实现另外两个特征：`Eq` 和 `PartialOrd`。

## `PartialOrd`

`PartialOrd` 是 `Ord` 的弱版本，就像 `PartialEq` 是 `Eq` 的弱版本。你可以通过查看其定义来了解原因：

```rs
pub trait PartialOrd: PartialEq {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>;
}
```

`PartialOrd::partial_cmp` 返回一个 `Option`——不能保证两个值可以比较。

例如，`f32` 没有实现 `Ord`，因为 `NaN` 值是不可比较的，这与 `f32` 没有实现 `Eq` 的原因相同。

## 实现 `Ord` 和 `PartialOrd`

`Ord` 和 `PartialOrd` 都可以为你的类型推导：

```rs
// You need to add `Eq` and `PartialEq` too,
// since `Ord` requires them.
#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct TicketId(u64);
```

如果你选择（或需要）手动实现它们，请小心：

+   `Ord` 和 `PartialOrd` 必须与 `Eq` 和 `PartialEq` 一致。

+   `Ord` 和 `PartialOrd` 必须相互一致。

## 练习

本节练习位于[`06_ticket_management/16_btreemap`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/16_btreemap)
