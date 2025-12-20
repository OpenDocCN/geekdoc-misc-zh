# 内部可变性

> 原文：[`rust-exercises.com/100-exercises/07_threads/06_interior_mutability.html`](https://rust-exercises.com/100-exercises/07_threads/06_interior_mutability.html)

让我们花点时间来推理 `Sender` 的 `send` 方法的签名：

```rs
impl<T> Sender<T> {
    pub fn send(&self, t: T) -> Result<(), SendError<T>> {
        // [...]
    }
}
```

`send` 方法以 `&self` 作为其参数。

但它显然引起了一种突变：它向通道添加了一条新消息。更有趣的是，`Sender` 是可克隆的：我们可以有多个 `Sender` 实例同时尝试修改通道状态，来自不同的线程。

这是我们构建这个客户端-服务器架构的关键属性。但为什么它有效？它不是违反 Rust 的借用规则吗？我们是如何通过一个**不可变**引用执行变动的？

## 共享而非不变引用

当我们引入借用检查器时，我们为 Rust 中可以拥有的两种引用类型命名：

+   不变引用（`&T`）

+   可变引用（`&mut T`）

更准确地说，应该这样命名它们：

+   共享引用（`&T`）

+   独占引用（`&mut T`）

不变/可变是一种适用于绝大多数情况的心理模型，也是 Rust 的一个很好的入门模型。但正如你所看到的，这并不是全部故事：`&T` 并不真正保证它指向的数据是不变的。

别担心，尽管如此：Rust 仍然在履行其承诺。只是这些条款比最初看起来要复杂一些。

## `UnsafeCell`

每当类型允许你通过共享引用修改数据时，你就是在处理**内部可变性**。

默认情况下，Rust 编译器假设共享引用是不变的。它根据这个假设**优化你的代码**。

编译器可以重新排序操作，缓存值，并执行各种魔法来使你的代码更快。

你可以通过将数据包裹在 `UnsafeCell` 中来告诉编译器：“不，这个共享引用实际上是可变的。”

每次你看到允许内部可变性的类型时，你可以确信 `UnsafeCell` 是涉及的，无论是直接还是间接的。

使用 `UnsafeCell`、原始指针和 `unsafe` 代码，你可以通过共享引用来修改数据。

让我们清楚地说明：`UnsafeCell` 不是一个魔法棒，可以让你忽略借用检查器！

`unsafe` 代码仍然受 Rust 关于借用和别名规则的约束。它是一个（高级）工具，你可以利用它来构建**安全的抽象**，其安全性不能直接在 Rust 的类型系统中表达。每次你使用 `unsafe` 关键字时，你都在告诉编译器：“我知道我在做什么，我不会违反你的不变性，相信我。”

每次调用 `unsafe` 函数时，都会有文档解释其**安全前提条件**：在什么情况下执行其 `unsafe` 块是安全的。你可以在 `std` 的文档中找到 `UnsafeCell` 的那些[文档](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)。

在本课程中，我们不会直接使用`UnsafeCell`，也不会编写`unsafe`代码。但了解它的存在、为什么存在以及它与你在 Rust 中每天使用的类型之间的关系是很重要的。

## 关键示例

让我们来看几个利用内部可变性的重要`std`类型。

这些是在 Rust 代码中你会经常遇到的类型，特别是如果你查看你使用的某些库的内部结构。

### 引用计数

`Rc`是一个引用计数的指针。

它围绕一个值进行包装，并跟踪有多少引用指向该值。当最后一个引用被丢弃时，该值将被释放。

包装在`Rc`中的值是不可变的：你只能获取对其的共享引用。

```rs
use std::rc::Rc;

let a: Rc<String> = Rc::new("My string".to_string());
// Only one reference to the string data exists.
assert_eq!(Rc::strong_count(&a), 1);

// When we call `clone`, the string data is not copied!
// Instead, the reference count for `Rc` is incremented.
let b = Rc::clone(&a);
assert_eq!(Rc::strong_count(&a), 2);
assert_eq!(Rc::strong_count(&b), 2);
// ^ Both `a` and `b` point to the same string data
//   and share the same reference counter.
```

`Rc`在内部使用`UnsafeCell`来允许共享引用增加和减少引用计数。

### `RefCell`

`RefCell`是 Rust 中内部可变性的最常见例子之一。它允许你在只有对`RefCell`本身的不可变引用的情况下，修改`RefCell`中包裹的值。

这是通过**运行时借用检查**来实现的。`RefCell`在运行时跟踪其包含的值的引用数量（和类型）。如果你在值已被不可变借用时尝试可变借用该值，程序将引发恐慌，确保 Rust 的借用规则始终得到执行。

```rs
use std::cell::RefCell;

let x = RefCell::new(42);

let y = x.borrow(); // Immutable borrow
let z = x.borrow_mut(); // Panics! There is an active immutable borrow.
```

## 练习

本节的练习位于[`07_threads/06_interior_mutability`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/06_interior_mutability)
