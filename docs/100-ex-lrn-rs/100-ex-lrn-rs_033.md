# 字符串切片

> 原文：[`rust-exercises.com/100-exercises/04_traits/06_str_slice.html`](https://rust-exercises.com/100-exercises/04_traits/06_str_slice.html)

在前面的章节中，你已经在代码中看到了很多**字符串字面量**的使用，比如`"To-Do"`或`"A ticket description"`。它们总是跟着`.to_string()`或`.into()`的调用。现在是时候理解为什么了！

## 字符串字面量

你通过将原始文本放在双引号中来定义一个字符串字面量：

```rs
let s = "Hello, world!";
```

`s`的类型是`&str`，是对字符串切片的**引用**。

## 内存布局

`&str`和`String`是不同的类型—they're not interchangeable.

让我们回顾一下从我们之前的探索中得到的`String`内存布局。如果我们运行：

```rs
let mut s = String::with_capacity(5);
s.push_str("Hello");
```

我们在内存中会得到这个场景：

```rs
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

如果你记得，我们也检查过一个`&String`在内存中的布局：

```rs
 --------------------------------------
     |                                    |         
+----v----+--------+----------+      +----|----+
| pointer | length | capacity |      | pointer |
|    |    |   5    |    5     |      |         |
+----|----+--------+----------+      +---------+
     |        s                          &s 
     |       
     v       
   +---+---+---+---+---+
   | H | e | l | l | o |
   +---+---+---+---+---+ 
```

`&String`指向存储`String`元数据的内存位置。

如果我们跟随指针，我们会到达堆分配的数据。特别是，我们会到达字符串的第一个字节，`H`。

如果我们想要一个表示`s`的**子字符串**的类型呢？例如，`ello`在`Hello`中？

## 字符串切片

一个`&str`是对字符串的一个**视图**，是对存储在其他地方的 UTF-8 字节序列的**引用**。例如，你可以这样从一个`String`创建一个`&str`：

```rs
let mut s = String::with_capacity(5);
s.push_str("Hello");
// Create a string slice reference from the `String`, 
// skipping the first byte.
let slice: &str = &s[1..];
```

在内存中，它看起来像这样：

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

`slice`在栈上存储了两条信息：

+   指向切片第一个字节的指针。

+   切片的长度。

`slice`不拥有数据，它只是指向它：它是`String`的堆分配数据的**引用**。

当`slice`被丢弃时，堆分配的数据不会被释放，因为它们仍然由`s`拥有。这就是为什么`slice`没有`capacity`字段的原因：它不拥有数据，因此不需要知道为它分配了多少空间；它只关心它引用的数据。

## `&str` vs `&String`

作为一条经验法则，当你需要一个文本数据的引用时，使用`&str`而不是`&String`。

`&str`更灵活，通常被认为在 Rust 代码中更符合习惯用法。

如果一个方法返回一个`&String`，你是在承诺某个地方有一个堆分配的 UTF-8 文本，它与你要返回的引用**完全匹配**。

如果一个方法返回一个`&str`，那么你就有更多的自由：你只是在说某个地方有一堆文本数据，其中的一部分与你需要的内容匹配，因此你返回对它的引用。

## 练习

本节练习位于[`04_traits/06_str_slice`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/06_str_slice)
