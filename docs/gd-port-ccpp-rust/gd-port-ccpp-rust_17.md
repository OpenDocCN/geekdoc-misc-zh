# Rust 的 std:: 库

# Rust 标准库

Rust 的核心功能由一个名为 `std` 的模块提供。这是标准运行时库。

与其 C++ 同名的情况类似，一切都可以通过 `std::` 命名空间前缀或通过 `use std::{foo}` 导入来引用。

Rust 的标准库中的一些内容通过特殊的 [`std::prelude`](https://doc.rust-lang.org/beta/std/prelude/) 隐式可用，自动使用（以及对 std crate 的引用）而无需声明。预设包含几乎所有代码可能使用的功能，因此 Rust 可以避免代码导入它：

+   字符串和 ToString 特性

+   各种迭代器特性 - Iterator、Exten、IntoIterator 等。

+   Result<> 和 Option<> 枚举

+   转换特性 AsRef、AsMut、Into、From

+   Vec 堆分配的向量

+   其他特性如 Drop、Fn、FnMut、FnOnce、Box、Clone、Copy、Send、Sized、Sync、PartialEq、PartialOrd 等。

+   宏例如 println!、format!、assert! 等。

```
// You don't need these
extern crate std;
use std::prelude::*; 
```

std 下有各种关注开发方面的子模块。以下只是其中一些：

1.  克隆 - 克隆特性

1.  cmp - Eq、Ord、PartialEq、PartialOrd 特性。这些特性用于相等性和排序功能。

1.  集合 - 包含序列、映射、集合和其他标准集合类型。例如 Vec 和 HashMap 属于这个模块。

1.  env - 环境辅助工具 - 命令行参数、状态码、环境变量、临时文件夹

1.  格式化和打印字符串的实用工具

1.  fs - 文件系统操作

1.  io - 由文件系统和网络中的流/缓冲区实现的 Read 和 Write 特性，stdio 功能

1.  内存原语

1.  网络 - 网络操作

1.  路径操作

1.  进程 - spawn、fork、exec 等

## C / C++ 到 Rust 库的交叉参考

待办事项

注意 Rust 的 std 命名空间包含许多标准 C 或 C++ 库中没有的内容，许多内容也没有直接类似。例如标准 C / C++ 库对套接字、路径操作、原子递增数字或创建线程几乎没有什么可说的。

| C | C++ | Rust |
| --- | --- | --- |
| T [S], 例如 char foo[20] | std::array (C++11) | [T; S], 例如 let foo: [u8; 20] = [0; 20] |
| char * 或带有函数如 strcmp、strcpy、strstr、strdup 等的 char[]。还有这些的宽字符等价物。 | std::string、std::wstring、std::u16string (C++11)、std::u32string (C++11) | 根据情况使用 &str 或 String |
| - | std::vector | std::vec::Vec 或 std::collections::VecDeque |
| - | std::list | std::collections::LinkedList |
| - | std::set | std::collections::HashSet, std::collections::BTreeSet |
| - | std::map | std::collections::HashMap, std::collections::BTreeMap |
| fopen、fclose、fread / fwrite、fseek 等 | std::ofstream、std::ifstream、std::fstream | 待办事项 |
| 诸如 cos、sin、tan、acos、asin、atan、pow、abs、log、log10、floor、ceil 等数学函数在<math.h class="hljs-meta"></math.h>中定义 | - | 数学函数可以从 f64\. f32 类型中直接访问，例如 1.0f64.cos()。 |

请注意，由于浮点数使用了小数点，因此在调用它们时必须给字面值加上 f32 或 f64 前缀，以便编译器能够理解你的意图。

## 标准特质

一些特质是系统定义的，在某些情况下可以自动派生。

在某些情况下，它们会导致编译器为你生成额外的代码，例如 Drop 特质（在类析构函数部分描述）。

### Drop

Drop 特质允许在对象被丢弃时执行一些操作，例如添加额外的日志记录或其他操作。

### Copy

实现 Copy 特质的结构体可以通过赋值进行复制，即如果你将 a 赋给 b，则 a 和 b 现在都有对象的副本，彼此独立。只有在你拥有表示某种类型或值的少量数据时，Copy 特质才真正有用。TODO 复制示例，例如结构体 PlayingCard { suit: Suit, rank: Rank } 如果你发现自己拥有的类型较大，或包含堆分配的内存，那么你应该使用 clone。

### Clone

实现 Clone 特质的结构体具有 .clone() 方法。与 Copy 不同，你必须显式地使用 .clone() 方法来创建另一个实例。TODO 克隆示例

### Eq、PartialEq

TODO 相等性

### Ord、PartialOrd

TODO 排序
