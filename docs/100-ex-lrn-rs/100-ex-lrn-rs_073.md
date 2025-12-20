# HashMap

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/15_hashmap.html`](https://rust-exercises.com/100-exercises/06_ticket_management/15_hashmap.html)

我们对 `Index`/`IndexMut` 的实现并不理想：我们需要遍历整个 `Vec` 来通过 id 检索票；算法的复杂度是 `O(n)`，其中 `n` 是存储中的票数。

我们可以通过使用不同的数据结构来存储票：一个 `HashMap<K, V>`。

```rs
use std::collections::HashMap;

// Type inference lets us omit an explicit type signature (which
// would be `HashMap<String, String>` in this example).
let mut book_reviews = HashMap::new();

book_reviews.insert(
    "Adventures of Huckleberry Finn".to_string(),
    "My favorite book.".to_string(),
);
```

`HashMap` 与键值对一起工作。它是通用的：`K` 是键类型的泛型参数，而 `V` 是值类型的泛型参数。

插入、检索和删除的预期成本是 **常数**，`O(1)`。这对我们的用例来说听起来很完美，不是吗？

## 键要求

在 `HashMap` 的结构定义上没有特征约束，但你会在其方法中找到一些。以 `insert` 为例：

```rs
// Slightly simplified
impl<K, V> HashMap<K, V>
where
    K: Eq + Hash,
{
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        // [...]
    }
}
```

键类型必须实现 `Eq` 和 `Hash` 特征。

让我们深入探讨这两个特征。

## 哈希

哈希函数（或哈希器）将一个可能无限大的值集（例如所有可能的字符串）映射到一个有界范围内（例如 `u64` 值）。

周围有许多不同的哈希函数，每个都有不同的属性（速度、冲突风险、可逆性等）。

如其名所示，`HashMap` 在幕后使用哈希函数。它将你的键进行哈希处理，然后使用该哈希值来存储/检索关联的值。这种策略要求键类型必须是可哈希的，因此对 `K` 有 `Hash` 特征约束。

你可以在 `std::hash` 模块中找到 `Hash` 特征：

```rs
pub trait Hash {
    // Required method
    fn hash<H>(&self, state: &mut H)
       where H: Hasher;
}
```

你很少会手动实现 `Hash`。大多数时候你会从它那里推导出来：

```rs
#[derive(Hash)]
struct Person {
    id: u32,
    name: String,
}
```

## 等价

`HashMap` 必须能够比较键的等价性。当处理哈希冲突时，这一点尤为重要——即当两个不同的键哈希到相同的值时。

你可能会想：那不正是 `PartialEq` 特征的作用吗？几乎是这样！

`PartialEq` 对于 `HashMap` 来说不够，因为它不保证自反性，即 `a == a` 总是 `true`。

例如，浮点数（`f32` 和 `f64`）实现了 `PartialEq`，但它们不满足自反性属性：`f32::NAN == f32::NAN` 是 `false`。

自反性对于 `HashMap` 正确工作至关重要：没有它，你将无法使用插入时使用的相同键从映射中检索值。

`Eq` 特征通过自反性属性扩展了 `PartialEq`：

```rs
pub trait Eq: PartialEq {
    // No additional methods
}
```

它是一个标记特征：它不添加任何新方法，它只是让你告诉编译器，在 `PartialEq` 中实现的等价逻辑是自反的。

当你从 `PartialEq` 继承时，可以自动推导出 `Eq`：

```rs
#[derive(PartialEq, Eq)]
struct Person {
    id: u32,
    name: String,
}
```

## 等价和哈希相关联

之间存在 `Eq` 和 `Hash` 的隐式契约：如果两个键相等，它们的哈希值也必须相等。这对于 `HashMap` 正确工作至关重要。如果你违反了这个契约，当使用 `HashMap` 时，你会得到无意义的输出。

## 练习

本节练习位于[`06_ticket_management/15_hashmap`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/15_hashmap)
