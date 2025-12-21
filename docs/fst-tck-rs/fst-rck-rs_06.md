# 包创建

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/package_creation.html`](https://freddiehaddad.github.io/fast-track-to-rust/package_creation.html)

让我们确保所有先决条件都已就绪。你应该已经遵循了安装说明来准备你的开发环境。完成这些步骤后，你应该能够运行以下命令：

```rs
$ rustc --version
rustc 1.81.0 (eeb90cda1 2024-09-04)

$ cargo --version
cargo 1.81.0 (2dbb1af80 2024-08-20) 
```

> 版本号可能不同，但输出应该相对相似。

如果上述命令都成功了，你就准备就绪了！

1.  使用 `cargo new rustle` 为我们的项目创建一个名为 `rustle` 的新 Rust 包：

    ```rs
    $ cargo new rustle
        Creating binary (application) `rustle` package
    note: see more `Cargo.toml` keys and their definitions at
    https://doc.rust-lang.org/cargo/reference/manifest.html 
    ```

1.  导航到 `rustle` 目录并使用 `cargo run` 来构建和运行程序：

    ```rs
    $ cd rustle
    $ cargo run
       Compiling rustle v0.1.0 (S:\projects\git\rustle)
        Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.43s
         Running `target\debug\rustle.exe`
    Hello, world! 
    ```

1.  使用 `cargo --help` 探索你可以使用 `cargo` 执行的其他操作。

    +   `cargo build` - 编译当前包

    +   `cargo build --release` - 以发布模式（带有优化）构建项目

    +   `cargo check` - 分析当前包并报告错误（不生成目标文件）

    +   `cargo test` - 运行单元测试

    +   和更多...

# 总结

在本节中，我们：

+   创建了一个包。

+   编译并运行了样板代码。

+   对 Cargo 有了一些了解。

# 下一节

让我们看看 `cargo new` 实际上做了什么！
