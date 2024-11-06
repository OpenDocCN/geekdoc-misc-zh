# 设置 Rust

# 设置 Rust

本节将指导您首次设置 Rust，以及如何保持其更新。

入门非常简单，但一些细节因目标平台而异。Rust 可在 Windows、Linux 和 MacOS 上运行。此外，您可能希望为另一个平台的消费交叉编译代码。

## 使用 Rustup

开始的最简单方法是下载并运行`rustup-init`，您可以通过访问[Rustup 网站](https://www.rustup.rs/)来执行。

说明针对 Windows 和类 Unix 系统有所不同：

+   在 Windows 上，rustup-init 是一个 exe 安装程序。

+   在 Unix / OS X / Linux 上，rust-init 是一个 shell 脚本。

无论哪种方式，当您按照说明操作时，安装程序将下载并安装 rustc、cargo 和 rustup 到您的 bin 目录，Unix 上为`~/.cargo/bin`，Windows 上为`%USERPROFILE%.cargo.\bin`。

它还会设置您的`PATH`环境变量，以便您可以打开终端并输入 rustc、cargo、rustup 等命令。

安装完`rustup`后，您还可以使用该工具进行维护：

+   安装额外的 Rust 工具链（例如，如果您要进行交叉编译或支持多个目标，则可能会有多个工具链）

+   更改默认的工具链，当您输入`rustc`或`cargo`时会调用该工具链。Rustup 将创建符号链接/脚本来调用适当的工具链。

+   当 Rust 发布新版本时更新工具链

+   获取源代码和文档

### Unix / Linux

运行`rustup-init.sh`的过程如下：

1.  打开一个终端/控制台

1.  输入 "curl [`sh.rustup.rs`](https://sh.rustup.rs) -sSf | sh"

1.  这将下载并执行一个脚本，该脚本将检查您的环境，推荐要下载的工具链，并提供修改您的`PATH`环境变量的选项。

1.  选择选项 1 继续。或者自定义如果您想修改一些内容

1.  等待下载完成

1.  完成。

如果您没有 curl，则必须先安装它才能继续，或者从浏览器保存[shell 脚本](https://sh.rustup.rs)到磁盘并执行该脚本。

要在 Linux 中安装`curl`，您需要调用类似这样的命令来安装它。

+   Debian / Ubuntu - `sudo apt get curl`

+   Fedora / Redhat - `sudo dnf install curl`

### Windows

1.  从 rustup.rs 下载 rustup-init.exe。

1.  双击 rust-init.exe，一个控制台将打开

1.  选择选项 1 继续。或者自定义如果您想修改一些内容

1.  等待下载完成

1.  完成。

如果您不想使用默认设置，这里有一些您应该决定的选择：

1.  32/64 位版本。如今大多数 Windows 安装都是 64 位的，但您可能有理由选择 32 位。

1.  GNU 或 MSVC ABI。这取决于您希望与之兼容的工具链和运行时。

第二个选择涉及您希望 Rust 兼容的应用程序二进制接口（ABI）。

+   如果你不关心链接到任何内容，那么选择 GNU ABI。如果你有由 MingW / MSYS 产生的 DLL，也选择它。这个 ABI 的优点是它更成熟。

+   如果你已经安装了 Visual Studio，或者打算使用 Rust 与 Visual Studio 创建的 DLL 进行交互，那么你需要选择这个 ABI。这个选项的一个优点是你可以在 Visual Studio 内部调试 Rust，编译器会生成允许你逐步调试 Rust 的 .pdb 文件。

### 保持 Rust 更新

Rust 的新版本会经常发布。如果你想将你的环境更新到最新版本，只需执行以下简单操作：

```
rustup update 
```

有时候 rustup 会有更新，这时你只需要输入：

```
rustup self update 
```

### 添加 Rust 源码

Rustup 安装了一个 Rust 工具链，但如果你要编写代码或进行调试，可能还需要获取 Rust 源代码，这样你就可以进行步进调试或查看实现代码：

```
rustup component add rust-src 
```

## 手动安装

如果你更喜欢手动安装 Rust，那么你可以在 [Rust 网站](https://www.rust-lang.org/en-US/downloads.html) 上找到相关的软件包和说明。

请注意，Rust 的发布周期相当快，因此只有当你有理由选择特定版本并坚持使用时，才需要手动安装。

否则，也许你会发现自己在 6 周后重新卸载和安装新版本。

## 设置调试器

### Unix / Linux

Rust 的调试与调试 C 或 C++ 有些不同。

你必须为你的平台安装 gdb，然后你可以从控制台或你喜欢的前端调用它来调试 Rust 代码。

在 Linux 系统上，你通常会使用以下其中一个命令来安装 gdb 软件包：

```
sudo apt-get install gdb
# or
sudo dnf install gdb 
```

你可能也更喜欢使用 lldb，它是 LLVM 的伴随项目（Rust 使用的后端编译器）。请参考 [lldb 网站](http://lldb.llvm.org/) 了解如何使用它。

Rust 自带一些包装 gdb 和 lldb 的脚本，以提供漂亮的打印输出，帮助调试。在调试时，你可以调用 `rust-gdb` 或 `rust-lldb` 来使用它们。

### Windows

如果你选择了使用 MSVC ABI 的 Rust，那么你可以通过 Visual Studio 进行调试，但有一些限制。当你创建代码的调试构建时，编译器也会创建一个 .pdb 文件。你可以在 Visual Studio 中打开可执行文件，进行逐步调试、检查变量等操作。

#### GDB

Windows 上的 GDB 可以通过 MSYS / MingW 发行版获得。

例如 TDM-GCC 分发的 MSYS 下载可以在 [这里](http://tdm-gcc.tdragon.net/download) 找到。在撰写本文时，有一个独立的 gdb-7.9.1-tdm64-2.zip，其中包含根据你的 Rust 环境选择的 32 位或 64 位版本。

将 zip 文件解压到一个目录，例如 `C:\tools\gdb-7.9.1-tdm64-2`，并将一个值添加到你的 `PATH` 环境变量中：

```
set PATH=%PATH%;C:\tools\gdb-7.9.1-tdm64-2\bin\ 
```

你可以从命令行中调用 `gdb`，但更常见的是你可能更喜欢一个前端。

在撰写本文时，也许最好的选择是 Visual Studio Code，它有用于使用 GDB 进行调试和 Rust 开发的插件。因此，您可以从同一个 IDE 编辑和调试。

##### 漂亮的打印机

Rust 提供了一个用于变量检查的漂亮打印机，你可以将其添加到 GDB 中。漂亮的打印机是一个用 Python 编写的脚本，GDB 将调用它来显示变量。

首先确保你的路径下安装了 Python 2.7。

该脚本与 Rust 源代码捆绑在一起，因此您首先需要安装它。

如果你用 `rustup` 安装它，那么它可以在你的 `%USERPROFILE%\.rustup` 目录下找到：

例如

```
c:\users\MyName\.rustup\toolchains\stable-x86_64-pc-windows-gnu\lib\rustlib\src\rust\src\etc 
```

否则，它可以在你解压 Rust 源代码的任何地方找到，例如 `src\rust\src\etc`。

注意完全限定的路径，以及使用*正斜杠*编辑 `C:\tools\gdb-7.9.1-tdm64-2\bin\gdbinit` 插入路径。

```
python
print "---- Loading Rust pretty-printers ----"

sys.path.insert(0, "C:/users/MyName/.rustup\toolchains/stable-x86_64-pc-windows-gnu/lib/rustlib/src/rust/src/etc")
import gdb_rust_pretty_printing
gdb_rust_pretty_printing.register_printers(gdb)

end 
```

## 设置一个集成开发环境（IDE）

当涉及到 IDE 集成时，Rust 还落后于一些其他语言，但已经有插件提供了您需要的大部分功能。

流行的 IDE，如 Eclipse、IntelliJ、Visual Studio，都有插件，与 Rust 集成的程度不同。

+   [Visual Studio Code](https://code.visualstudio.com/) （不要与 Visual Studio 混淆）是一个跨平台的编程编辑器，拥有大量插件。通过按照这个 [教程](https://sherryummen.in/2016/09/02/debugging-rust-on-windows-using-visual-studio-code/) 进行设置，它可以成为一个完整的 Rust 开发环境。

+   [Rust plugin for IntelliJ IDEA](https://intellij-rust.github.io/) 正在积极开发中。该插件受到了很多关注，并且几乎每周都发布新版本。提供语法高亮、自动补全（通过内置解析器）、cargo 构建以及最终其他功能。[IntelliJ](https://www.jetbrains.com/idea/download/#section=windows) 是一个商业产品，但它有一个足够用于开发的社区版。

+   [Visual Rust plugin for Microsoft Studio](https://github.com/PistonDevelopers/VisualRust) 。提供语法高亮、自动补全、交互式调试。

+   [RustDT for Eclipse](https://github.com/RustDT/RustDT) 也在积极开发中。它为 Eclipse 添加了语法高亮、自动补全（通过 racer）、cargo 构建和 rustfmt 功能。

+   Atom 是一个拥有大量插件的流行编辑器。这些插件在 Rust 中非常有用：

    +   [language-rust](https://atom.io/packages/language-rust) 提供基本的语法高亮

    +   [racer](https://atom.io/packages/racer) 提供自动补全功能

    +   [atom-beautify](https://atom.io/packages/atom-beautify) 调用 rustfmt 使代码看起来漂亮。

    +   [build-cargo](https://atom.io/packages/build-cargo) 为您调用 cargo，显示内联错误和警告。

对于其他编辑器和 IDE，请参考 Rust 网站上的 [Rust and IDEs](https://forge.rust-lang.org/ides.html) 页面。

## Racer / Rustfmt

上面的一些插件使用了 Racer 和 Rustfmt。

一些插件使用 Racer 提供自动补全功能。

Rustfmt 是一个源代码格式化工具，确保你的 Rust 源代码看起来漂亮，添加空格、缩进等。

通过输入这些命令并等待工具下载和构建自身，你可以同时获得它们 - 它们是用 Rust 编写的，并通过 cargo 构建。

```
cargo install racer
cargo install rustfmt 
```
