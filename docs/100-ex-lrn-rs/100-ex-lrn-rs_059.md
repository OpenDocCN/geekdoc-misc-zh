# 数组

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/01_arrays.html`](https://rust-exercises.com/100-exercises/06_ticket_management/01_arrays.html)

一旦我们开始谈论“票务管理”，我们就需要考虑一种存储 *多个* 票的方法。反过来，这意味着我们需要考虑集合。特别是同质集合：我们希望存储同一类型的多个实例。

Rust 在这方面能提供什么？

## 数组

第一次尝试可能会使用 **数组**。

Rust 中的数组是相同类型元素的固定大小集合。

这是你定义数组的方法：

```rs
// Array type syntax: [ <type> ; <number of elements> ]
let numbers: [u32; 3] = [1, 2, 3];
```

这将创建一个包含 3 个整数的数组，并初始化为值 `1`、`2` 和 `3`。

数组的类型是 `[u32; 3]`，读作“长度为 3 的 `u32` 数组”。

如果所有数组元素都相同，你可以使用更短的语法来初始化它：

```rs
// [ <value> ; <number of elements> ]
let numbers: [u32; 3] = [1; 3];
```

`[1; 3]` 创建了一个包含三个元素且所有元素都等于 `1` 的数组。

### 访问元素

你可以使用方括号访问数组的元素：

```rs
let first = numbers[0];
let second = numbers[1];
let third = numbers[2];
```

索引必须是 `usize` 类型。

数组是 **零索引** 的，就像 Rust 中的所有东西一样。你之前在字符串切片和元组的字段索引中见过。

### 越界访问

如果你尝试访问超出边界的元素，Rust 将会引发恐慌：

```rs
let numbers: [u32; 3] = [1, 2, 3];
let fourth = numbers[3]; // This will panic
```

这在运行时通过 **边界检查** 来强制执行。它带来了一些性能开销，但这是 Rust 防止缓冲区溢出的方法。

在某些场景中，Rust 编译器可以优化掉边界检查，特别是如果涉及到迭代器时——我们稍后会更多地讨论这一点。

如果你不希望引发恐慌，可以使用 `get` 方法，它返回一个 `Option<&T>`：

```rs
let numbers: [u32; 3] = [1, 2, 3];
assert_eq!(numbers.get(0), Some(&1));
// You get a `None` if you try to access an out-of-bounds index
// rather than a panic.
assert_eq!(numbers.get(3), None);
```

### 性能

由于数组的大小在编译时已知，编译器可以在栈上分配数组。如果你运行以下代码：

```rs
let numbers: [u32; 3] = [1, 2, 3];
```

你将得到以下内存布局：

```rs
 +---+---+---+
Stack:  | 1 | 2 | 3 |
        +---+---+---+ 
```

换句话说，数组的大小是 `std::mem::size_of::<T>() * N`，其中 `T` 是元素类型，`N` 是元素数量。

你可以在 `O(1)` 时间内访问和替换每个元素。

## 练习

本节练习位于 `06_ticket_management/01_arrays` 中，请参阅[此处](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/01_arrays)。
