# 移植代码

# 移植代码

在开始之前，此时的假设是您 *需要* 迁移代码。如果您不确定自己是否需要迁移代码，那么也许您不需要。毕竟，如果您的 C/C++ 代码运行良好，为什么要改变呢？

TODO 本节将提供一个更真实的 C/C++ 示例，并将其移植到等效的 Rust 代码中

## 自动化工具

### Corrode

[Corrode](https://github.com/jameysharp/corrode) 是一个命令行工具，可以部分地将 C 转换为 Rust。至少它可能会让您省去一些劳动力，确保功能尽可能接近原始功能。

Corrode 将接受一个 C 文件，例如 `somefile.c`，再加上 `gcc` 的任何参数，并生成一个 `somefile.rs`，其中包含 Rust 中的等效代码。

它的工作原理是将 C 代码解析为抽象语法树，然后从中生成 Rust 代码。

有趣的是，Corrode 是用 Haskell 编写的，更有趣的是它是以 [literate Haskell source](https://github.com/jameysharp/corrode/blob/master/src/Language/Rust/Corrode/C.md) 的形式编写的 - 代码是一个与 Haskell 穿插的 Markdown 文档。

### Bindgen

[Bindgen](https://github.com/servo/rust-bindgen) 是一个用于从现有 C 和 C++ 头文件生成 Rust 的 FFI 接口的工具。如果您正在从 C/C++ 迁移代码，或者编写一个必须与现有代码库一起工作的新组件，您可能会发现这很有用。

Bindgen 需要您预先安装 Clang C++ 编译器，以便将代码解析为它可以消化的结构。

网站链接上的自述文件提供了有关安装和使用该工具的更多信息。

## 经验

一些网站提供了从 C 移植到 Rust 的过程的见解

1.  [将 Zopfli 从 C 移植到 Rust](https://github.com/carols10cents/rust-out-your-c-talk)。Zopfli 是一个执行良好但速度较慢的 deflate 算法库。它产生的压缩文件比 zlib 更小，同时仍然与之兼容。

1.  TODO

# 提示

## 尽可能使用引用

TODO 引用等效于 C++ 中的引用或 C 中的指针。通过引用传递是将任何大于 64 位的对象高效地传递到函数中而不放弃所有权的方法。在某些情况下，甚至通过引用返回也是一个好主意，因为调用者始终可以克隆对象（如果需要的话），而且往往他们只需使用引用，只要生命周期允许。

TODO 对于诸如整数、布尔等固有类型，您不需要使用引用，除非您打算使它们可变并更改。

## 学习移动语义

C 和 C++ 默认是赋值时复制，而 Rust 在赋值时会移动，除非该类型实现了 `Copy` 特性。这很容易是新的 Rust 程序员会遇到的最令人费解的事情之一。在 C++ 中完美运行的代码在 Rust 中会立即失败。

克服这一问题的方法首先是使用引用，其次是不要移动，除非您打算接收者成为对象的新所有者。

TODO 如果你希望接收方拥有对象的副本，则在你的结构体上实现 Clone 特质。然后你可以调用`.clone()`，接收方将成为克隆的所有者，而不是你的副本。

## 使用模块自然地组织你的源代码

TODO

## 使用组合和特质

TODO Rust 不允许你从另一个结构体继承。克服这一点的方法。

## 使用 Cargo.toml 创建你的构建配置文件

## 使用 Rust 命名规范和格式化

C 和 C++ 从未有过

# 外部函数接口

TODO 现在阅读 [FFI omnibus](http://jakegoulding.com/rust-ffi-omnibus/)。

## 保留函数名称不变

TODO 添加 no_mangle 属性

## libc

TODO Rust 提供了一个包含 C 库函数绑定的 crate。如果你发现自己接收到通过 malloc 分配的指针，你可以通过绑定调用对应的 free() 来释放它。

TODO 将以下内容添加到你的`Cargo.toml`中

```
[dependencies]
libc = "*" 
```

TODO 使用 libc 的示例
