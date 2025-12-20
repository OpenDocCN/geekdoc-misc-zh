# 依赖项

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/11_dependencies.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/11_dependencies.html)

一个包可以通过在其 `Cargo.toml` 文件的 `[dependencies]` 部分中列出其他包来依赖于其他包。

指定依赖项最常见的方式是提供其名称和版本：

```rs
[dependencies]
thiserror = "1" 
```

这将为您的包添加 `thiserror` 作为依赖项，其 **最小** 版本为 `1.0.0`。`thiserror` 将从 [crates.io](https://crates.io)，Rust 的官方包注册处获取。当您运行 `cargo build` 时，`cargo` 将经过几个阶段：

+   依赖项解析

+   下载依赖项

+   编译您的项目（您的代码和依赖项）

如果您的项目有一个 `Cargo.lock` 文件且您的清单文件未更改，则将跳过依赖项解析。`cargo` 在成功的一轮依赖项解析后自动生成锁文件：它包含项目中使用的所有依赖项的确切版本，并用于确保在不同构建（例如在 CI 中）中始终使用相同的版本。如果您在一个有多个开发者的项目上工作，您应该将 `Cargo.lock` 文件提交到您的版本控制系统。

您可以使用 `cargo update` 来更新 `Cargo.lock` 文件，使其包含所有依赖项的最新（兼容）版本。

### 路径依赖

您也可以使用 **路径** 来指定依赖项。当您在多个本地包上工作时，这很有用。

```rs
[dependencies]
my-library = { path = "../my-library" } 
```

路径相对于声明依赖项的包的 `Cargo.toml` 文件是相对的。

### 其他来源

查阅 [Cargo 文档](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)，了解更多关于您可以从哪里获取依赖项以及如何在您的 `Cargo.toml` 文件中指定它们的信息。

## 开发依赖

您也可以指定仅用于开发的依赖项——即只有在您运行 `cargo test` 时才会被拉入。

它们位于您的 `Cargo.toml` 文件的 `[dev-dependencies]` 部分：

```rs
[dev-dependencies]
static_assertions = "1.1.0" 
```

我们在整本书中使用了其中的一些来缩短我们的测试。

## 练习

本节练习位于 [05_ticket_v2/11_dependencies](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/11_dependencies)
