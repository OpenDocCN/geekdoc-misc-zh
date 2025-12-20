# 特质

> [`rust-exercises.com/100-exercises/04_traits/00_intro.html`](https://rust-exercises.com/100-exercises/04_traits/00_intro.html)

在上一章中，我们介绍了 Rust 的类型和所有权系统的基本概念。

是时候深入挖掘了：我们将探讨**特质**，Rust 对接口的看法。

一旦你了解了特质，你将开始到处看到它们的痕迹。

实际上，你已经在上一章中看到了特质的实际应用，例如`.into()`调用以及`==`和`+`这样的运算符。

除了特质这个概念之外，我们还将介绍 Rust 标准库中定义的一些关键特质：

+   运算符特质（例如`Add`、`Sub`、`PartialEq`等）

+   `From`和`Into`，用于不可靠的转换

+   `Clone`和`Copy`，用于复制值

+   `Deref`和解引用强制转换

+   `Sized`，用于标记已知大小的类型

+   `Drop`，用于自定义清理逻辑

由于我们将讨论转换，我们将抓住机会填补上一章的一些“知识空白”——例如，“`A title`”究竟是什么？现在是时候更多地了解切片了！

## 练习

本节练习位于[`04_traits/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/00_intro)
