# 值的复制，第一部分

> 原文：[`rust-exercises.com/100-exercises/04_traits/11_clone.html`](https://rust-exercises.com/100-exercises/04_traits/11_clone.html)

在上一章中，我们介绍了所有权和借用。

我们特别指出：

+   在任何给定时间，Rust 中的每个值都有一个单一的所有者。

+   当一个函数接受一个值的所有权时（“它消耗了它”），调用者不能再使用该值。

这些限制可能有些限制性。

有时我们可能需要调用一个接受值所有权的函数，但我们仍然需要在该函数之后使用该值。

```rs
fn consumer(s: String) { /* */ }

fn example() {
     let mut s = String::from("hello");
     consumer(s);
     s.push_str(", world!"); // error: value borrowed here after move
}
```

这就是 `Clone` 发挥作用的地方。

## `Clone` 特性

`Clone` 是 Rust 标准库中定义的一个特质：

```rs
pub trait Clone {
    fn clone(&self) -> Self;
}
```

它的方法 `clone` 接收对 `self` 的引用并返回相同类型的新 **拥有** 实例。

## 实战

回到上面的例子，我们可以在调用 `consumer` 之前使用 `clone` 创建一个新的 `String` 实例：

```rs
fn consumer(s: String) { /* */ }

fn example() {
     let mut s = String::from("hello");
     let t = s.clone();
     consumer(t);
     s.push_str(", world!"); // no error
}
```

我们不是将 `s` 的所有权交给 `consumer`，而是创建一个新的 `String`（通过克隆 `s`）并将其交给 `consumer`。

在调用 `consumer` 之后，`s` 仍然有效且可使用。

## 内存中的情况

让我们看看上面例子中内存中发生了什么。当执行 `let mut s = String::from("hello");` 时，内存看起来像这样：

```rs
 s
      +---------+--------+----------+
Stack | pointer | length | capacity | 
      |  |      |   5    |    5     |
      +--|------+--------+----------+
         |
         |
         v
       +---+---+---+---+---+
Heap:  | H | e | l | l | o |
       +---+---+---+---+---+ 
```

当执行 `let t = s.clone()` 时，在堆上分配了一个全新的区域来存储数据的副本：

```rs
 s                                    t
      +---------+--------+----------+      +---------+--------+----------+
Stack | pointer | length | capacity |      | pointer | length | capacity |
      |  |      |   5    |    5     |      |  |      |   5    |    5     |
      +--|------+--------+----------+      +--|------+--------+----------+
         |                                    |
         |                                    |
         v                                    v
       +---+---+---+---+---+                +---+---+---+---+---+
Heap:  | H | e | l | l | o |                | H | e | l | l | o |
       +---+---+---+---+---+                +---+---+---+---+---+ 
```

如果你来自像 Java 这样的语言，你可以将 `clone` 视为创建对象深拷贝的一种方式。

## 实现 `Clone` 特性

要使类型 `Clone`-able，我们必须为它实现 `Clone` 特性。

你几乎总是通过派生来实现 `Clone`：

```rs
#[derive(Clone)]
struct MyType {
    // fields
}
```

编译器按照预期为 `MyType` 实现 `Clone`：它单独克隆 `MyType` 的每个字段，然后使用克隆的字段构建一个新的 `MyType` 实例。

记住，你可以使用 `cargo expand`（或你的 IDE）来探索由 `derive` 宏生成的代码。

## 练习

本节的练习位于 [`04_traits/11_clone`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/11_clone)
