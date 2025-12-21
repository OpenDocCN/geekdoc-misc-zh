# Cargo.toml

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/cargo_toml.html`](https://freddiehaddad.github.io/fast-track-to-rust/cargo_toml.html)

`Cargo.toml`是`cargo new`生成的样板文件之一。这是我们管理依赖项和其他配置的地方。起始文件相当简单。

```rs
[package]
name = "rustle"
version = "0.1.0"
edition = "2021"

[dependencies] 
```

## 添加依赖项

添加依赖项就像在`Cargo.toml`文件的`[dependencies]`部分指定 crate 的名称和所需版本^(1)一样简单。以下是如何添加`regex`crate 的示例。

```rs
regex = "1.11.1" 
```

我们还可以使用`cargo add`：

```rs
$ cargo add regex
    Updating crates.io index
      Adding regex v1.11.1 to dependencies
             Features:
             + perf
             + perf-backtrack
             + perf-cache
             + perf-dfa
             + perf-inline
             + perf-literal
             + perf-onepass
             + std
             + unicode
             + unicode-age
             + unicode-bool
             + unicode-case
             + unicode-gencat
             + unicode-perl
             + unicode-script
             + unicode-segment
             - logging
             - pattern
             - perf-dfa-full
             - unstable
             - use_std
    Updating crates.io index
     Locking 5 packages to latest compatible versions
      Adding aho-corasick v1.1.3
      Adding memchr v2.7.4
      Adding regex v1.11.1
      Adding regex-automata v0.4.9
      Adding regex-syntax v0.8.5 
```

两种方法都会产生相同的结果。

```rs
[package]
name = "rustle"
version = "0.1.0"
edition = "2021"

[dependencies]
regex = "1.11.1" 
```

# 练习

> 这些练习必须在本地完成。

+   添加`clap`crate 并包含`derive`^(2)功能。更多关于如何完成此操作的信息可以在[这里](https://crates.io/crates/clap)和[这里](https://docs.rs/clap/latest/clap/_derive/_tutorial/chapter_0/index.html)找到。

<details><summary>解决方案</summary>

```rs
clap = { version = "4.5.21", features = ["derive"] }
regex = "1.11.1" 
```</details>

* * *

1.  支持语义版本号（即[SemVer](https://semver.org/)）。有关更高级的版本控制，请参阅[指定依赖项](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies)的文档。↩

1.  在依赖声明中可以启用依赖项的功能。功能键指示要启用哪些功能。《Cargo 手册》（[Cargo Book](https://doc.rust-lang.org/cargo/index.html)）在[依赖项功能](https://doc.rust-lang.org/cargo/reference/features.html#dependency-features)部分对此进行了介绍。↩
