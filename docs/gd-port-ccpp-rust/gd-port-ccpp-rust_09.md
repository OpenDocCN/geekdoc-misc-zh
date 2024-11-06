# 编译和链接更详细

# 编译和链接更详细

## 您的 main()入口点

Rust 有一个类似于 C/C++的 main 函数，通常称为`main()`。^（1）

它不带任何参数，也不像 C/C++那样返回任何内容。让我们看看如何做这些事情。

### 处理命令行参数

在 C/C++中，入口点接受 argc 和 argv 参数。Argc 是参数的数量，argv 是指定这些参数的 char *指针数组。

```
int main(int arcg, char **argv) {
  // our code
} 
```

处理参数可能变得异常复杂（和有错误），因此大多数软件将使用诸如`getopt()`或`getopt_long()`之类的函数来简化该过程。

注意，`getopt()`不是标准的 C 函数，也不是可移植的，例如到 Windows。因此，我们立即看到了 C/C++强制我们解决的问题的一个例子。

Rust 不会以这种方式处理参数。相反，您可以从代码的任何地方访问`std::env::args()`中的命令行参数。也就是说，有一个名为`args()`的函数位于`std::env`命名空间下，它返回命令行上的字符串。

函数`args()`返回一个字符串数组中的参数。与 C++类似，数组的第一个元素在索引 0 处是命令本身：

```
use std::env;
fn main() {
    for argument in env::args() {
        println!("{}", argument);
    }
} 
```

或者，由于`args()`返回一个实现了`Iterator` trait 的类型`Args`，您可以将参数收集到您自己的集合中并处理它：

```
use std::env;
use std::collections::HashSet;
fn main() {
    let args: HashSet<String> = env::args().collect();
    let verbose_flag = args.contains("--verbose");
} 
```

我们可以看到 Rust 提供参数的一些明显优势：

+   您不需要一个独立的 argc 参数。您有一个定义自己长度的数组。

+   您可以从程序的任何地方访问参数，而不仅仅是从`main()`中。在 C++中，您必须将参数从一个地方传递到另一个地方。在 Rust 中，您可以从任何地方简单地请求它们。

#### 使用 crate - 简单的命令行处理

Rust 有许多用于处理参数的 crate。用于处理参数的最流行的 crate 是[clap](https://crates.io/crates/clap)。

它提供了一种非常描述性的、声明式的方式将处理参数的规则添加到代码中。如果您的程序接受大量参数，包括参数和验证规则，那么它尤其有用。

例如，我们将这个添加到`Cargo.toml`中：

```
[dependencies]
clap = "2.27" 
```

在我们的`main.rs`中。

```
#[macro_use] extern crate clap;
use clap::*;
fn main() {
  let matches = App::new("Sample App")
    .author("My Name <myname@foocorp.com>")
    .about("Sample application")
    .arg(Arg::with_name("T")
        .long("timetowait")
        .help("Waits some period of time for something to happen")
        .default_value("10")
        .takes_value(true)
        .possible_values(&["10", "20", "30"])
        .required(false))
    .get_matches();

  let time_to_wait = value_t_or_exit!(matches, "T", u32);
  println!("Time to wait value is {}", time_to_wait);
} 
```

此代码将处理`-T`或`--timetowait`的参数，并确保值是 3 个接受的值之一。如果用户没有提供值，则默认为`10`。如果用户没有提供有效的整数，它将用有用的错误终止应用程序。

用户还可以提供`--help`作为参数，它将打印出用法。

### 退出代码

如果要退出并返回代码，则需显式设置它：

```
fn main() {
    //... my code
    std::os::set_exit_status(1);
} 
```

当`main()`退出时，运行时会清理并将代码返回给环境。再次强调，状态码没有必要在`main()`中设置，您可以将其设置在其他地方，并通过`panic!()`导致应用程序退出。

## 优化编译

在典型的编辑/编译/调试循环中，没有必要优化代码，因此除非您要求，否则 Rust 不会进行优化。

优化需要更长的时间，并且可能重新排列代码，以至于回溯和调试可能不会指向源代码中的正确行。

如果您想优化您的代码，请向 rustc 添加一个-O 参数：

```
rustc -O hw.rs 
```

优化的行为将导致 Rust 在链接之前调用 LLVM 优化器。这将产生更快的可执行代码，但会增加编译时间。

## 增量编译

增量编译对于编辑/编译/调试循环也很重要。增量编译只重新构建那些通过修改而发生变化的代码部分，以最小化重建产品所需的时间。

Rust 具有与 C++不同的增量编译模型。

+   C++本身不支持增量编译。这个功能留给了 make/project/solution 工具。大多数构建工具将跟踪一个项目文件列表以及哪个文件依赖于其他文件。因此，如果文件 foo.h 发生变化，那么构建工具知道依赖于它的其他文件，并确保在重新链接目标可执行文件之前重新构建它们。

+   在 Rust 中，增量编译是在 crate 级别进行的 - 如果一个 crate 中的任何文件发生变化，则整个 crate 都必须重新构建。因此，较大的代码库往往会被拆分成 crates 以减少增量构建时间。

Rust 社区认识到 crate 级别模型对于大型 crate 来说可能不太好，因此 Rust 编译器正在获得[每个文件增量编译支持](https://blog.rust-lang.org/2016/09/08/incremental.html)，除了每个 crate。

在撰写本文时，此支持是实验性的，因为它与重构编译器以改进性能和优化的其他原因相关联���但最终将由 rustc 和 cargo 启用和支持。

## 管理一个项目

在 C++中，我们会使用一个`makefile`或某种解决方案文件来管理一个真实世界的项目并构建它。

对于小程序，我们可能会运行一个脚本或直接调用编译器，但随着程序的增长和构建时间的延长，我们将不得不使用一个`makefile`来保持我们的理智。

典型的`makefile`包含规则，说明哪些文件是我们的源文件，每个源文件如何依赖其他源文件（如头文件），我们的最终可执行文件是什么，以及一堆关于必须维护的编译和链接标志的其他混乱内容。

多年来出现了许多不同的 makefile 解决方案，但一个简单的 gmake 可能看起来像这样：

```
SRCS = main.o pacman.o sprites.o sfx.o
OBJS = $(SRCS:.cpp=.o)
EXE = pacman
$(EXE): $(OBJS)
    $(CC) $(CFLAGS) -o $(EXE) $(OBJS)
.cpp.o:
    $(CC) $(CFLAGS) -c $< -o $@ 
```

当您调用`make`时，软件将检查目标的所有依赖项，查看它们的文件时间戳，并确定需要调用哪些规则以及以何种顺序重建您的代码。

Rust 使事情变得更容易 - 没有 makefile！源代码就是 makefile。每个文件通过对其他 crate 和其他模块的依赖来说明它使用了哪些其他文件。

考虑这个 pacman 游戏的 main.rs：

```
mod pacman;

fn main() {
  let mut game = pacman::Game::new();
  game.start();
} 
```

如果我们保存了这个文件并键入`rustc main.rs`，编译器将注意到对`mod pacman`的引用，并且将搜索`pacman.rs`（或`pacman/mod.rs`）并编译它。它将继续处理沿途引用的任何其他模块。

换句话说，您可以拥有一个包含 1000 个文件的项目，并且只需简单地编译`rustc main.rs`。任何被引用的内容都会自动编译和链接。

好吧，我们可以调用`rustc`，但是如果我们的代码有其他项目的依赖关系会发生什么？或者我们的项目是为了被导出，以便其他项目可以使用它？

### Cargo

Cargo 是一个集成了包管理器和构建工具的工具。Cargo 可以获取依赖项，构建它们，构建和链接您的代码，运行单元测试，安装二进制文件，生成文档，并将项目的版本上传到存储库。

在 Rust 中创建新项目的最简单方法是使用`cargo`命令来完成

```
cargo new hello_world –bin 
```

创建此

```
hello_world/
  .git/ (git repo)
  .gitignore
  Cargo.toml
  src/
    main.rs 
```

构建项目只是这样的一个简单过程：

```
cargo build 
```

如果您想要构建发布版本，可以添加一个--release 参数。这将调用 rust 编译器启用优化：

```
cargo build --release 
```

如果我们想要在代码中构建和运行单元测试，我们可以编写

```
cargo test 
```

### 箱子和外部依赖项

Cargo 不仅负责构建我们的代码，还确保我们的代码所依赖的任何内容也被下载和构建。这些外部依赖项在我们项目根目录中的`Cargo.toml`中定义。

我们可以编辑该文件以表示我们对外部"箱子"（如`time`箱子）有一个依赖关系：

```
[package]
name = "hello_world"
version = "0.1.0"
authors = ["Joe Blogs <jbloggs@somewhere.com>"]

[dependencies]
time = "0.1.35" 
```

现在当我们运行`cargo build`时，它将从 crates.io 获取"time"，以及"time"本身所具有的任何依赖项。然后它会自动按顺序构建每个箱子。它会高效地执行此操作，因此迭代构建不会产生任何惩罚。外部箱子会下载并构建在您的.cargo 主目录中。

要使用我们的外部箱子，我们在我们代码的 main.rs 中声明它，例如。

```
extern crate time;

fn main() {
  let now = time::PreciseTime::now();
  println!("The time is {:?}", now);
} 
```

因此，对`Cargo.toml`的更改和源代码中的引用就足够了：

1.  获取箱子（以及任何依赖项）

1.  构建箱子（以及任何依赖项）

1.  编译并链接到箱子和依赖项

所有这些都只是在`Cargo.toml`中加一行，在我们的代码中加一行来引用箱子。我们不必费心弄清楚如何构建其他库，或者维护多个 makefile，或者正确设置我们的编译器/链接器标志。这一切都是自动完成的。

#### Cargo.lock

还要注意，一旦我们构建，cargo 会在我们的根目录下创建一个`Cargo.lock`文件。

这个文件是这样制作的，以便如果再次调用`cargo build`，它就会有一个确切的列表，需要拉取和编译哪些包。它避免了代码（可以这么说）在我们脚下移动并突然我们的项目无法构建的情况。因此，如果锁定文件存在，则甚至可以从干净的状态重现相同的依赖配置。如果要强制 cargo 重新构建一个新的锁定文件，例如在更改了`Cargo.toml`后，可以输入`cargo update`。

> ¹. 如果你想要改变主入口点，可以使用特殊的`#[start]`指令指定另一个函数，但默认是`main()`。 ↩
