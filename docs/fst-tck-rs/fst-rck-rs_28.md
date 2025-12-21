# 模块

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/modules.html`](https://freddiehaddad.github.io/fast-track-to-rust/modules.html)

*模块*帮助我们组织 crate 内的代码，以实现更好的可读性和易于重用。它们还允许我们控制项目的*隐私性*，因为模块内的代码默认是私有的。私有项是内部实现细节，不可从外部访问。我们可以选择使模块及其项公开，以便外部代码使用和依赖。

请参考 Rust 文档中关于[定义模块以控制作用域和隐私](https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html#defining-modules-to-control-scope-and-privacy)的部分。

# 摘要

在本节中，我们介绍了以下内容：

+   crate：一个生成库或可执行文件的模块树

+   包：一个允许你构建、测试和共享 crate 的货物特性

+   模块：让你控制项目的组织

# 下一节

在对 crate、包和模块有基本了解之后，让我们利用其中一个来支持正则表达式。
