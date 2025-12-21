# 属性

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/attributes.html`](https://freddiehaddad.github.io/fast-track-to-rust/attributes.html)

在本课程中，我们一直在使用 [属性](https://doc.rust-lang.org/reference/attributes.html)，但我们还没有深入探讨。让我们简要地讨论一下你遇到过的属性，并提供一些有用的资源以供进一步探索。

在高层次上，属性是应用于 crate、模块或项目的元数据。这些元数据服务于各种目的。属性遵循以下语法：

```rs
InnerAttribute :
   # ! [ Attr ]

OuterAttribute :
   # [ Attr ]

Attr :
      SimplePath AttrInput?
   | unsafe ( SimplePath AttrInput? )

AttrInput :
      DelimTokenTree
   | = Expression 
```

属性有两种形式：`InnerAttribute` 和 `OuterAttribute`。它们之间的区别在于 `InnerAttribute` 在 `#` 和 `` 之间包含一个感叹号 (`!`)。`InnerAttribute` 适用于其声明的项目，而 `OuterAttribute` 适用于其后面的任何内容。

## [内部属性

例如，在我们的 rustle 程序中，我们使用了内联属性 `#![allow(unused_imports)]`。默认情况下，Rust 编译器如果发现你的程序通过 `use` 导入的包实际上没有使用，会发出警告。我们的程序通过 `use std::fs::File;` 导入了 `File` 模块，但由于我们正在使用 `Cursor` 进行开发，并且已经注释掉了文件 I/O 代码，编译器会抱怨未使用的导入。这个属性禁用了这个警告。

## 外部属性

回想一下，在上一个章节中，我们通过 `#[derive(...)]` 属性推导了 `Debug` 和 `PartialEq` 特性。我们通过将这个属性直接放置在 `Interval` 结构体的定义之前来实现这一点。这是一个 `OuterAttribute` 的例子。

```rs
#[derive(Debug, PartialEq)]
pub struct Interval<T> {
    pub start: T,
    pub end: T,
}
```

## 属性分类

属性通常被分为以下几类：

+   [内置属性](https://doc.rust-lang.org/reference/attributes.html#built-in-attributes-index)

+   [宏属性](https://doc.rust-lang.org/reference/procedural-macros.html#attribute-macros)

+   [派生宏辅助属性](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macro-helper-attributes)

+   [工具属性](https://doc.rust-lang.org/reference/attributes.html#tool-attributes)

# 摘要

[Rust 参考文档](https://doc.rust-lang.org/reference/) 对 [属性](https://doc.rust-lang.org/reference/attributes.html) 进行了深入探讨，你被鼓励去探索它以获得对它们用途的全面理解。此外，[Rust By Example](https://doc.rust-lang.org/rust-by-example/) 提供了额外的材料，并展示了各种 [用例](https://doc.rust-lang.org/rust-by-example/attribute.html)。

# 下一节

属性提供了更大的实用性，我们将通过命令行参数解析来探讨这一点！
