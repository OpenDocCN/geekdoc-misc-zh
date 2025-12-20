# 内存布局

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/08_stack.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/08_stack.html)

我们已经从操作的角度探讨了所有权和引用——你可以用它们做什么，不能做什么。现在是时候揭开盖子看看了：让我们来谈谈**内存**。

## 栈和堆

当讨论内存时，你经常会听到人们谈论**栈**和**堆**。

这些是程序用来存储数据的两个不同的内存区域。

让我们从栈开始。

## 栈

**栈**是一个**后进先出**（LIFO）的数据结构。

当你调用一个函数时，一个新的**栈帧**会被添加到栈顶。这个栈帧存储了函数的参数、局部变量和一些“记账”值。

当函数返回时，栈帧会被从栈中弹出^(1)。

```rs
+-----------------+
| frame for func1 |
+-----------------+
        |
        | func2 is 
        | called
        v
+-----------------+
| frame for func2 |
+-----------------+
| frame for func1 |
+-----------------+
        |
        | func2  
        | returns
        v
+-----------------+
| frame for func1 |
+-----------------+ 
```

从操作的角度来看，栈的分配/释放是非常快的。

我们总是从栈顶推入和弹出数据，所以我们不需要搜索空闲内存。我们也不必担心碎片化：栈是一个单一的连续内存块。

### Rust

Rust 经常会将数据分配在栈上。

你在函数中有一个`u32`输入参数？这 32 位将会在栈上。

你定义了一个类型为`i64`的局部变量？这 64 位将会在栈上。

所有这些都工作得相当好，因为这些整数的尺寸在编译时是已知的，因此编译后的程序知道它需要为它们在栈上预留多少空间。

### `std::mem::size_of`

你可以使用`[`std::mem::size_of](https://doc.rust-lang.org/std/mem/fn.size_of.html)`函数来验证一个类型在栈上会占用多少空间。

例如，对于一个`u8`：

```rs
// We'll explain this funny-looking syntax (`::<u8>`) later on.
// Ignore it for now.
assert_eq!(std::mem::size_of::<u8>(), 1);
```

1 有意义，因为`u8`是 8 位长，或者说 1 字节。

## 练习

本节练习位于[`03_ticket_v1/08_stack`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/08_stack)

* * *

1.  如果你有多层嵌套的函数调用，每个函数在调用时会将其数据推入栈中，但它不会在内部函数返回之前将其弹出。如果你有太多的嵌套函数调用，你可能会耗尽栈空间——栈不是无限的！这被称为[**栈溢出**](https://en.wikipedia.org/wiki/Stack_overflow)。↩
