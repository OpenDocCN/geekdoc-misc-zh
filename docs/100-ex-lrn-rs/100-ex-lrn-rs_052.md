# 库和二进制程序

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/10_packages.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/10_packages.html)

实现对 `TicketNewError` 的 `Error` 特性确实需要一些代码，不是吗？

一个手动实现的 `Display` 和一个 `Error` 实现块。

我们可以通过使用提供简化自定义错误类型创建的 **过程宏** 的 Rust crate `thiserror` 来移除一些样板代码。

但我们可能有些过于急躁了：`thiserror` 是一个第三方 crate，这将是我们的第一个依赖项！

在我们深入研究依赖项之前，让我们退一步来谈谈 Rust 的打包系统。

## 什么是包？

Rust 包由 `Cargo.toml` 文件中的 `[package]` 部分定义，也称为其 **清单**。在 `[package]` 中，你可以设置包的元数据，例如其名称和版本。

去检查这个部分练习的目录下的 `Cargo.toml` 文件！

## 什么是 crate？

在包内部，你可以有一个或多个 **crate**，也称为 **目标**。

两种最常见的 crate 类型是 **二进制 crate** 和 **库 crate**。

### 二进制程序

二进制程序是可以编译成 **可执行文件** 的程序。

它必须包含一个名为 `main` 的函数——程序的入口点。当程序执行时，会调用 `main`。

### 库

相反，库本身是不可执行的。你不能 *运行* 一个库，但你可以从依赖于它的另一个包中 *导入* 其代码。

库将代码（即函数、类型等）组合在一起，其他包可以作为 **依赖项** 利用。

你至今为止解决的所有练习都已被结构化为库，并且附带了测试套件。

### 约定

在 Rust 包周围有一些约定，你需要记住：

+   包的源代码通常位于 `src` 目录中。

+   如果有一个 `src/lib.rs` 文件，`cargo` 会推断出该包包含一个库 crate。

+   如果有一个 `src/main.rs` 文件，`cargo` 会推断出该包包含一个二进制 crate。

你可以通过在 `Cargo.toml` 文件中明确声明你的目标来覆盖这些默认设置——有关更多详细信息，请参阅 [cargo 的文档](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#cargo-targets)。

请记住，虽然一个包可以包含多个 crate，但它只能包含一个库 crate。

## 练习

本节练习位于 [05_ticket_v2/10_packages](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/10_packages)
