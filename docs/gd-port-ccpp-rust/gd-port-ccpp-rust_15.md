# 调试 Rust

# 调试 Rust

Rust 编译成机器码与 C 相同，并且从与 C/C++ 相同的 ABI 和编译器后端格式共享的好处。

所以你可以像调试 C/C++ 一样调试 Rust。如果你的 Rust 可执行文件是在兼容 gcc 的二进制格式下构建的，你可以直接调用 gdb：

```
gdb my_executable 
```

Rust 自带一个名为 `rust-gdb` 的 gdb 包装脚本，该脚本加载了执行语法高亮的宏。

## 启用回溯

如果你的代码因为`panic!()`而崩溃，你可以通过设置`RUST_BACKTRACE`环境变量在控制台上获得回溯。

```
# Windows
set RUST_BACKTRACE=1
# Unix/Linux
export RUST_BACKTRACE=1 
```

## 找出你的目标二进制格式

如果你不确定你的目标是什么，你可以使用 `rustup` 来显示。

```
c:\dev\visu>rustup show
Default host: x86_64-pc-windows-msvc

stable-x86_64-pc-windows-msvc (default)
rustc 1.13.0 (2c6933acc 2016-11-07) 
```

或者：

```
[foo@localhost ~]$ rustup show
Default host: x86_64-unknown-linux-gnu

stable-x86_64-unknown-linux-gnu (default)
rustc 1.13.0 (2c6933acc 2016-11-07) 
```

信息将告诉你可以使用哪个调试器来调试你的代码。

### Microsoft Visual Studio

如果你有 MSVC 工具链（32 位或 64 位）或 LLVM 后端将生成一个 .pdb 文件，二进制文件将与标准的 MSVC 运行时兼容。

调试你的代码：

1.  打开 Visual Studio

1.  选择 文件 | 打开 | 项目/解决方案...

1.  选择编译后的可执行文件

1.  打开要调试的源文件并设置断点

1.  点击“开始”按钮

### GDB

GDB 可以直接从命令行调用，也可以通过插件/IDE 调用。从命令行调用它是一个

待办事项

### LLDB

待办事项
