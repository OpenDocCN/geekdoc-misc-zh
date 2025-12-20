# Sized

> 原文：[`rust-exercises.com/100-exercises/04_traits/08_sized.html`](https://rust-exercises.com/100-exercises/04_traits/08_sized.html)

即使在调查了解引用强制转换之后，`&str`还有更多内容。它不仅仅是表面上的东西。

从我们之前关于内存布局的讨论，我们合理地预期`&str`在栈上应该表示为一个单独的`usize`，即一个指针。但这并不是事实。`&str`在指针旁边存储了一些**元数据**：它指向的切片的长度。回到之前章节的例子：

```rs
let mut s = String::with_capacity(5);
s.push_str("Hello");
// Create a string slice reference from the `String`, 
// skipping the first byte.
let slice: &str = &s[1..];
```

在内存中，我们得到：

```rs
 s                              slice
      +---------+--------+----------+      +---------+--------+
Stack | pointer | length | capacity |      | pointer | length |
      |    |    |   5    |    5     |      |    |    |   4    |
      +----|----+--------+----------+      +----|----+--------+
           |        s                           |  
           |                                    |
           v                                    | 
         +---+---+---+---+---+                  |
Heap:    | H | e | l | l | o |                  |
         +---+---+---+---+---+                  |
               ^                                |
               |                                |
               +--------------------------------+ 
```

发生了什么？

## 动态大小类型

`str`是一个**动态大小类型**（DST）。

DST 是一种在编译时大小未知的数据类型。每当你有 DST 的引用，如`&str`，它必须包含关于它指向的数据的额外信息。它是一个**胖指针**。

在`&str`的情况下，它存储了它指向的切片的长度。我们将在课程剩余部分看到更多 DST 的例子。

## `Sized`特性

Rust 的`std`库定义了一个名为`Sized`的特性。

```rs
pub trait Sized {
    // This is an empty trait, no methods to implement.
}
```

如果一个类型的大小在编译时已知，则该类型是`Sized`。换句话说，它不是一个 DST。

### 标记特性

`Sized`是**标记特性**的第一个例子。

标记特性是一种不需要实现任何方法的特性。它不定义任何行为。它只用于**标记**一个类型具有某些属性。然后，标记被编译器利用以启用某些行为或优化。

### 自动特性

特别是，`Sized`也是一个**自动特性**。

你不需要显式实现它；编译器会根据类型的定义自动为你实现。

### 示例

我们到目前为止看到的所有类型都是`Sized`：`u32`、`String`、`bool`等。

`str`，正如我们刚才看到的，不是`Sized`。

`&str`虽然是`Sized`的！我们知道它在编译时的大小：两个`usize`，一个用于指针，一个用于长度。

## 练习

本节的练习位于[`04_traits/08_sized`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/08_sized)
