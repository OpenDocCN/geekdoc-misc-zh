# 欢迎加入

> 原文：[`rust-exercises.com/100-exercises/01_intro/00_welcome.html`](https://rust-exercises.com/100-exercises/01_intro/00_welcome.html)

欢迎加入 **“100 练习学习 Rust”**！

本课程将一次一个练习地教你 Rust 的核心概念。

你将了解 Rust 的语法、其类型系统、其标准库以及其生态系统。

我们不假设你对 Rust 有任何先前的知识，但我们假设你至少了解另一种编程语言。我们也不假设你对系统编程或内存管理有任何先前的知识。这些主题将在课程中介绍。

换句话说，我们将从头开始！

你将通过小而可控的步骤逐步构建你的 Rust 知识。课程结束时，你将完成约 ~100 个练习，这足以让你在小型到中型 Rust 项目上感到舒适。

## 方法论

本课程基于“实践学习”原则。

它被设计成互动和动手实践。

[Mainmatter](https://mainmatter.com/rust-consulting/) 开发了这门课程，以便在教室环境中进行，为期 4 天：每位参与者根据自己的进度学习课程，有经验讲师提供指导，解答问题，并在需要时深入探讨主题。

你可以在我们的网站上注册下一次辅导课程（[我们的网站](https://ti.to/mainmatter/rust-from-scratch-jan-2025)）。如果你想为你的公司组织一个私人课程，请[联系我们](https://mainmatter.com/contact/)。

你也可以独立完成这些课程，但我们建议如果你遇到困难，可以找一个朋友或导师来帮助你。你可以在 GitHub 仓库的 `solutions` 分支中找到所有练习的解决方案（[GitHub 仓库的 solutions 分支](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/solutions)）。

## 格式

你可以通过浏览器浏览课程材料（[在浏览器中浏览课程材料](https://rust-exercises.com/100-exercises/)）或将其作为 PDF 文件下载（[下载 PDF 文件](https://rust-exercises.com/100-exercises-to-learn-rust.pdf)），进行离线阅读。

如果你希望打印课程材料，可以在 Amazon 上购买平装本（[在 Amazon 上购买平装本](https://www.amazon.com/dp/B0DJ14KQQG/)）。

## 结构

在屏幕左侧，你可以看到课程被分为几个部分。每个部分介绍 Rust 语言的一个新概念或特性。

为了验证你的理解，每个部分都配有一个需要解决的练习。

你可以在配套的 GitHub 仓库中找到练习（[配套 GitHub 仓库](https://github.com/mainmatter/100-exercises-to-learn-rust)）。

在开始课程之前，请确保将仓库克隆到你的本地机器上：

```rs
# If you have an SSH key set up with GitHub
git clone git@github.com:mainmatter/100-exercises-to-learn-rust.git
# Otherwise, use the HTTPS URL:
#   https://github.com/mainmatter/100-exercises-to-learn-rust.git 
```

我们还建议你在分支上工作，这样你可以轻松跟踪你的进度，并在需要时从主仓库中拉取更新：

```rs
cd 100-exercises-to-learn-rust
git checkout -b my-solutions 
```

所有练习都位于`exercises`文件夹中。每个练习都结构为一个 Rust 包。该包包含练习本身、操作说明（在`src/lib.rs`中），以及一个测试套件来自动验证你的解决方案。

### 工具

为了完成这门课程，你需要：

+   [**Rust**](https://www.rust-lang.org/tools/install)。如果`rustup`已经安装在你的系统上，运行`rustup update`（或根据你在系统上安装 Rust 的方式的其他适当命令）以确保你运行的是最新稳定版本。

+   *(可选但推荐)* 一个支持 Rust 自动补全的 IDE。我们推荐以下之一：

    +   [RustRover](https://www.jetbrains.com/rust/)

    +   [Visual Studio Code](https://code.visualstudio.com) 配置了`rust-analyzer`扩展。

### 研讨会运行者，`wr`

为了验证你的解决方案，我们还提供了一个工具来引导你完成课程：`wr` CLI，即“研讨会运行者”。按照[其网站](https://mainmatter.github.io/rust-workshop-runner/)上的说明安装`wr`。

安装好`wr`后，打开一个新的终端并导航到存储库的顶级文件夹。运行`wr`命令以开始课程：

```rs
wr 
```

`wr`将验证当前练习的解决方案。

在解决当前练习之前，不要进入下一节。

> 我们建议你在课程进展过程中将解决方案提交到 Git，这样你可以轻松跟踪进度，并在需要时从已知点“重启”。

享受这门课程吧！

## 作者

本课程由[Luca Palmieri](https://www.lpalmieri.com/)编写，他是[Mainmatter](https://mainmatter.com/rust-consulting/)的首席工程顾问。

Luca 自 2018 年以来一直在使用 Rust，最初在 TrueLayer，后来在 AWS。

Luca 是《["从零开始学习 Rust"](https://zero2prod.com)》的作者，这是学习如何在 Rust 中构建后端应用的必备资源。

他也是各种开源 Rust 项目的作者和维护者，包括[`cargo-chef`](https://github.com/LukeMathWalker/cargo-chef)、[Pavex](https://pavex.dev)和[`wiremock`](https://github.com/LukeMathWalker/wiremock-rs)。

## 练习

本节练习位于[`01_intro/00_welcome`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/01_intro/00_welcome)
