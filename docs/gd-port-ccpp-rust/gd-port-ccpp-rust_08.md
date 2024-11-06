# 让我们从简单的开始

# 让我们从简单的开始

任何语言的通常介绍都是"Hello, World!"。一个将该消息打印到控制台的简单程序。

这是我们如何为 C 编写它的方式：

```
#include <stdio.h>

int main(int argc, char *argv[]) {
  printf("Hello, World!\n");
  return 0;
} 
```

C++可以以相同的方式编写，或者如果我们更喜欢的话，可以使用 C++的流类：

```
#include <iostream>

using namespace std;

int main(int argc, char *argv[]) {
  cout << "Hello, World!" << endl;
  return 0;
} 
```

这里是 Rust 中的等效部分：

```
fn main() {
  println!("Hello, World!");
} 
```

我们可以观察到一些明显的相似之处：

+   C/C++和 Rust 都遵循将`main()`函数作为代码入口点的约定。注意，Rust 的 main 函数不返回任何内容。它实际上是一个空方法。

+   有一个通用的打印语句。

+   在主要方面的一般结构，即主要部分，使用{ }和分号大部分相同。在两种语言中，一段代码被大括号括起来，分号用作语句之间的分隔符。

+   Rust 看起来比 C 或 C++更为简洁，因为它自动包含对其称为"预导入"的标准运行时的部分的引用。

`println!()`实际上是一个宏，它会扩展成写入标准输出的代码。我们知道它是一个宏，因为它以一个!字符结尾，但是你现在可以将它视为一个函数调用。我们将在后面看到 Rust 宏与 C/C++中的宏有何不同。

## 编译我们的代码

打开命令提示符并设置您的编译器环境。

如果你使用 gcc，你会像这样编译你的代码：

```
gcc hw.cpp -o hw 
```

如果你使用 Microsoft Visual C++，你会这样编译：

```
cl /o hw.exe hw.cpp 
```

要在 Rust 中编译，你需要调用 rustc 编译器。

```
rustc hw.rs 
```

并运行其中一个

```
./hw (or .\hw.exe)
Hello, World! 
```

再次有相似之处：

+   有一个 shell 命令，用于编译代码并创建可执行文件。

+   二进制文件以相同的方式运行。

一个不太明显的相似之处是 Rust 与 gcc-llvm 和 clang 共享其代码生成后端。Rustc 输出 llvm 比特码，通过 LLVM 编译（和优化）成机器码。这意味着生成的可执行文件在形式上与 C++编译器输出的非常相似。这包括它为调试目的提供的符号信息。一个 Rust 可执行文件可以在 gdb、lldb 或 Microsoft Visual Studio 中进行调试，具体取决于目标平台。

```
rustc -O hw.rs 
```
