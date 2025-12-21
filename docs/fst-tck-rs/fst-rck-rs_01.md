# 欢迎来到 Fast Track to Rust

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/index.html`](https://freddiehaddad.github.io/fast-track-to-rust/index.html)

本课程旨在通过构建一个实际程序来向您介绍 Rust 编程语言。我们将开发一个类似 grep 的程序，称为 rustle^(1)，它具有 [GNU](https://www.gnu.org/) ^(2) [grep](https://www.gnu.org/software/grep/manual/grep.html) ^(3) 工具中找到的最小功能集。这意味着我们将从已知的内容开始，随着对语言的了解加深，我们将迭代设计。

> 本在线课程的官方网址是：[`freddiehaddad.github.io/fast-track-to-rust`](https://freddiehaddad.github.io/fast-track-to-rust)
> 
> 源代码可以在以下位置找到：[`github.com/freddiehaddad/fast-track-to-rust`](https://github.com/freddiehaddad/fast-track-to-rust)

目标是教会您 Rust，因此假设您对该语言一无所知。然而，也假设您有在其他语言（如 C++）中编程的经验，并且熟悉多线程、数据结构和程序内存组织（即堆、栈等）。

本课程进展相对较快。大多数主题都涵盖了足够的内容，以提供基本理解。随着您的进步，将提供官方 Rust [文档](https://doc.rust-lang.org/book/title-page.html)的引用，以便进一步探索。

足够闲聊了，让我们开始吧！

![Fast Track to Rust Logo](img/78d3819ae7275566f3e27d1c2dd2384a.png)

* * *

1.  选择 Rustle 这个名字是因为它与“rust”这个词的谐音，代表着程序在搜索数据时树叶沙沙作响的声音。↩

1.  GNU 是一组常用的免费软件集合，通常用作操作系统。被称为 Linux 的操作系统家族就是由它们构建的。↩

1.  Grep 搜索一个或多个输入文件，查找包含指定模式的行。默认情况下，grep 输出匹配的行。↩
