# Crates

> [`freddiehaddad.github.io/fast-track-to-rust/crates.html`](https://freddiehaddad.github.io/fast-track-to-rust/crates.html)

Crates 是 Rust 编译器一次处理的代码的最小单位。例如，我们正在开发的 rustle 程序被 Rust 编译器识别为一个 crate。

## Crates 类型

Crates 有两种类型：二进制和库。编译器根据是否存在 `main.rs` 或 `lib.rs` 文件来识别正在编译的 crate 的类型。

### 二进制 Crates

二进制 Crates 包含 `src` 目录中的 `main.rs` 文件，具有 `main` 函数，并且会被编译成可执行文件。

### 库 Crates

库 Crates 包含 `src` 目录中的 `lib.rs` 文件，没有主函数，并且不会编译成可执行文件。相反，它们被设计成可以与其他项目共享。
