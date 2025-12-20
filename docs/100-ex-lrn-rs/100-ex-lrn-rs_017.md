# 模块

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/03_modules.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/03_modules.html)

你刚刚定义的`new`方法试图对`Ticket`的字段值施加一些**约束**。但这些不变量真的被强制执行了吗？什么阻止开发者不通过`Ticket::new`创建`Ticket`？

要获得适当的**封装**，你需要熟悉两个新概念：**可见性**和**模块**。让我们从模块开始。

## 什么是模块？

在 Rust 中，**模块**是一种将相关代码组合在一起的方式，在公共命名空间（即模块的名称）下。

你已经看到了模块的实际应用：验证你的代码正确性的单元测试定义在名为`tests`的不同模块中。

```rs
#[cfg(test)]
mod tests {
    // [...]
}
```

## 内联模块

上面的`tests`模块是一个**内联模块**的例子：模块声明（`mod tests`）和模块内容（`{ ... }`内的内容）是相邻的。

## 模块树

模块可以嵌套，形成**树**结构。

树的根是**crate**本身，这是包含所有其他模块的最高级模块。对于一个库 crate，根模块通常是`src/lib.rs`（除非其位置已被自定义）。根模块也被称为**crate 根**。

crate 的根目录可以有子模块，这些子模块又可以有自己的子模块，以此类推。

## 外部模块和文件系统

内联模块对于小块代码很有用，但随着你的项目增长，你可能希望将代码拆分成多个文件。在父模块中，你使用`mod`关键字声明子模块的存在。

```rs
mod dog;
```

`cargo`，Rust 的构建工具，负责找到包含模块实现的文件。

如果你的模块在 crate 的根目录下声明（例如`src/lib.rs`或`src/main.rs`），`cargo`期望文件被命名为以下之一：

+   `src/<module_name>.rs`

+   `src/<module_name>/mod.rs`

如果你的模块是另一个模块的子模块，文件应该命名为：

+   `[..]/<parent_module>/<module_name>.rs`

+   `[..]/<parent_module>/<module_name>/mod.rs`

例如`src/animals/dog.rs`或`src/animals/dog/mod.rs`，如果`dog`是`animals`的子模块。

你的 IDE 可能会在你使用`mod`关键字声明新模块时自动创建这些文件。

## 项目路径和`use`语句

你可以无特殊语法地访问同一模块中定义的项目。你只需使用它们的名称。

```rs
struct Ticket {
    // [...]
}

// No need to qualify `Ticket` in any way here
// because we're in the same module
fn mark_ticket_as_done(ticket: Ticket) {
    // [...]
}
```

如果你想从一个不同的模块访问一个实体，情况就不同了。

你必须使用指向你想要访问的实体的**路径**。

你可以用各种方式组合路径：

+   从当前 crate 的根目录开始，例如`crate::module_1::MyStruct`

+   从父模块开始，例如`super::my_function`

+   从当前模块开始，例如`sub_module_1::MyStruct`

`crate`和`super`都是**关键字**。

`crate`指的是当前 crate 的根，而`super`指的是当前模块的父模块。

每次你想引用一个类型时都必须写出完整的路径可能会很麻烦。为了使你的生活更轻松，你可以引入一个`use`语句来将实体引入作用域。

```rs
// Bring `MyStruct` into scope
use crate::module_1::module_2::MyStruct;

// Now you can refer to `MyStruct` directly
fn a_function(s: MyStruct) {
     // [...]
}
```

### 星号导入

你也可以使用单个`use`语句从模块中导入所有项目。

```rs
use crate::module_1::module_2::*;
```

这被称为**星号导入**。

这通常是不被推荐的，因为它可能会污染当前命名空间，使得难以理解每个名称的来源，并可能引入名称冲突。

尽管如此，在某些情况下它可能很有用，比如在编写单元测试时。你可能已经注意到，我们的大部分测试模块都以`use super::*;`语句开始，以便将父模块（被测试的模块）中的所有项目引入作用域。

## 可视化模块树

如果你难以想象你项目的模块树，你可以尝试使用[`cargo-modules`](https://crates.io/crates/cargo-modules)来可视化它！

请参考它们的文档以获取安装说明和使用示例。

## 练习

本节的练习位于[`03_ticket_v1/03_modules`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/03_modules)
