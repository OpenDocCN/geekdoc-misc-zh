# Drop 特性

> 原文：[`rust-exercises.com/100-exercises/04_traits/13_drop.html`](https://rust-exercises.com/100-exercises/04_traits/13_drop.html)

当我们介绍 析构函数 时，我们提到 `drop` 函数：

1.  重新回收类型占用的内存（即 `std::mem::size_of` 字节）

1.  清理值可能管理的任何额外资源（例如 `String` 的堆缓冲区）

第 2 步是 `Drop` 特性出现的地方。

```rs
pub trait Drop {
    fn drop(&mut self);
}
```

`Drop` 特性是一个机制，允许你为你的类型定义*额外*的清理逻辑，这超出了编译器为你自动执行的范围。

你在 `drop` 方法中放入的任何内容都会在值超出作用域时执行。

## `Drop` 和 `Copy`

当我们谈论 `Copy` 特性时，我们说如果一个类型在内存中占用的 `std::mem::size_of` 字节数之外管理了额外资源，那么它就不能实现 `Copy`。

你可能会想知道：编译器是如何知道一个类型管理了额外资源的？没错：`Drop` 特性实现！

如果你的类型有显式的 `Drop` 实现，编译器将假设你的类型附加了额外资源，并且不允许你实现 `Copy`。

```rs
// This is a unit struct, i.e. a struct with no fields.
#[derive(Clone, Copy)]
struct MyType;

impl Drop for MyType {
    fn drop(&mut self) {
       // We don't need to do anything here,
       // it's enough to have an "empty" Drop implementation
    }
}
```

编译器会显示以下错误信息：

```rs
error[E0184]: the trait `Copy` cannot be implemented for this type; 
              the type has a destructor
 --> src/lib.rs:2:17
  |
2 | #[derive(Clone, Copy)]
  |                 ^^^^ `Copy` not allowed on types with destructors 
```

## 练习

本节的练习位于 `04_traits/13_drop` 中（[`github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/13_drop`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/13_drop)）
