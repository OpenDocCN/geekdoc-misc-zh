# 项目管理

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/project_management.html`](https://freddiehaddad.github.io/fast-track-to-rust/project_management.html)

随着程序规模的扩大，有效地组织代码变得至关重要。通过将相关功能分组并分离不同的特性，您可以更容易地找到负责特定特性的代码，并修改该特性的操作方式。让我们看看 Rust 项目是如何组织的。

将 Rust 文档中的内容进行释义，Rust 提供了多个特性来帮助您管理代码的组织，包括哪些细节是公开的，哪些是私有的，以及每个程序作用域中的名称。这些特性通常统称为模块系统，包括：

+   **包**：Cargo 的一个特性，允许您构建、测试和共享包。

+   **包**：一个生成库或可执行文件的模块树。

+   **模块**和**use**：允许您控制路径的组织、作用域和隐私。

+   **路径**：命名一个项的方式，例如结构体、函数或模块。

关于项目管理的所有详细信息都可以在 [《Rust 编程语言》文档的“使用包、包和模块管理不断增长的项目”部分](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html#managing-growing-projects-with-packages-crates-and-modules) 中找到。
