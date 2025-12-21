# 样板代码

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/boilerplate.html`](https://freddiehaddad.github.io/fast-track-to-rust/boilerplate.html)

在前一节中，我们使用 `cargo new` 创建了一个 Rust 包，这是创建包最常见的方式。运行此命令生成了一些样板代码。当我们使用 `cargo run` 时，会创建一个 `target` 目录，并调用 Rust 编译器 `rustc`，在 `target` 目录内生成编译器相关文件和一个可执行二进制文件。

使用 `cargo clean` 清理一切，并返回到样板代码。`cargo clean` 命令会删除所有生成代码所在的目标目录。运行 `cargo clean` 后，我们将只剩下样板代码。

```rs
$ cargo clean
     Removed 23 files, 2.9MiB total 
```

```rs
.
+ Cargo.lock
+ Cargo.toml
+ src
  + main.rs 
```

目前，我们将专注于 `main.rs`，稍后讨论 `Cargo.lock` 和 `Cargo.toml`。

## main.rs

`main.rs` 是一个 Rust 源文件，它是作为包的一部分创建的。它包含一个名为 `main` 的函数，该函数作为程序的入口点。

`main.rs` 的内容：

```rs
fn main() {
    println!("Hello, world!");
}
```

一些语法可能看起来很熟悉：

+   代码块由花括号 `{}` 包围。

+   语句以分号 `;` 结尾。

+   函数参数用括号 `()` 括起来。

+   字符串字面量用双引号 `""` 括起来。

可能不熟悉的内容：

+   `fn` 是用于声明函数的关键字。

+   `println!` 实际上是一个宏，由 `!` 后缀表示。

# 摘要

在本节中，我们：

+   探索了 `cargo new` 生成的样板代码。

+   检查了一些基本的 Rust 语法。

# 下一节

让我们深入构建我们的 rustle 程序。我们将从设置基本结构开始，然后逐渐添加更多功能。
