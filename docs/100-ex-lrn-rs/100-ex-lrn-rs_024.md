# 参考文献

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/10_references_in_memory.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/10_references_in_memory.html)

关于像`&String`或`&mut String`这样的引用，它们在内存中是如何表示的呢？

在 Rust 中，大多数引用^(1)在内存中都是以指向内存位置的指针形式表示的。

因此，它们的大小与指针的大小相同，即`usize`。

你可以使用`std::mem::size_of`来验证这一点：

```rs
assert_eq!(std::mem::size_of::<&String>(), 8);
assert_eq!(std::mem::size_of::<&mut String>(), 8);
```

特别是，一个`&String`是一个指向存储`String`元数据的内存位置的指针。

如果你运行这个片段：

```rs
let s = String::from("Hey");
let r = &s;
```

你在内存中会得到类似这样的结果：

```rs
 --------------------------------------
           |                                    |
      +----v----+--------+----------+      +----|----+
Stack | pointer | length | capacity |      | pointer |
      |  |      |   3    |    5     |      |         |
      +--|  ----+--------+----------+      +---------+
         |          s                           r
         |
         v
       +---+---+---+---+---+
Heap   | H | e | y | ? | ? |
       +---+---+---+---+---+ 
```

如果你想知道，它是一个指向堆分配数据的指针的指针。对于`&mut String`也是同样的道理。

## 并非所有指针都指向堆

上面的例子应该可以澄清一点：并不是所有的指针都指向堆。

它们仅仅指向一个内存位置，这个位置*可能*在堆上，但也不一定。

## 练习

本节的学习练习位于[`03_ticket_v1/10_references_in_memory`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/10_references_in_memory)

* * *

1.  课程后续部分我们将讨论**胖指针**，即带有额外元数据的指针。正如其名所示，它们比本章讨论的指针要大，也被称为**瘦指针**。↩
