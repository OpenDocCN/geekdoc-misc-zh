# 创建模块

> [原文链接](https://freddiehaddad.github.io/fast-track-to-rust/creating_modules.html)

在上一节中，我们定义了一个`enum`和`struct`。然而，我们实际上并没有创建一个模块！在本节中，我们将这样做。在深入细节之前，Rust 文档提供了一个[模块速查表](https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html#modules-cheat-sheet)，这将是你 Rust 之旅中的一个方便的参考。

由于我们正在构建的模块是为了在这个在线书中工作，我们将稍微偏离标准实践。通常，模块是在单独的文件中创建的。例如，我们的`Interval`将被放置在一个名为`interval.rs`的新文件中。

```rs
rustle
+ Cargo.lock
+ Cargo.toml
+ src
  + interval.rs
  + main.rs 
```

> 文档生成
> 
> 随着我们开发我们的`interval`模块，这是一个了解[`rustdoc`](https://doc.rust-lang.org/rustdoc/index.html)和文档生成的好机会。`interval`模块将被注释以启用文档生成。如果你是在本地构建代码，生成和查看文档的最简单方法是使用`cargo doc --open`。

让我们开始吧！
