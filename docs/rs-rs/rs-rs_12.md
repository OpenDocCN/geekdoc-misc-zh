# 第十二章：无标准库的 Rust

![](img/chapterart.png)

Rust 旨在成为一种系统编程语言，但它究竟意味着什么并不总是显而易见。至少，系统编程语言通常被期望允许程序员编写不依赖操作系统并可以直接在硬件上运行的程序，无论这个硬件是一个千核超级计算机，还是一个拥有 72MHz 时钟速度和 256KiB 内存的单核 ARM 嵌入式设备。

在本章中，我们将探讨如何在非常规环境中使用 Rust，例如没有操作系统的环境，或者那些甚至无法动态分配内存的环境！我们的讨论将重点关注`#![no_std]`属性，但我们也将研究 Rust 的`alloc`模块、Rust 的运行时（是的，Rust 确实有一个运行时）以及在这种环境中编写 Rust 二进制文件时需要采用的一些技巧。

## 放弃标准库

作为一门语言，Rust 由多个独立的部分组成。首先是编译器，它规定了 Rust 语言的语法，并实现了类型检查、借用检查以及最终转换为机器可运行代码的过程。然后是标准库`std`，它实现了大多数程序需要的所有常用功能——例如文件和网络访问、时间的概念、打印和读取用户输入的功能等。但`std`本身也是一个复合体，建立在两个更基础的库`core`和`alloc`之上。事实上，`std`中的许多类型和函数只是从这两个库重新导出的。

`core`库位于标准库金字塔的底部，包含任何仅依赖于 Rust 语言本身和程序运行时硬件的功能——如排序算法、标记类型、基础类型如`Option`和`Result`、低级操作如原子内存访问方法以及编译器提示等。`core`库的工作方式就像操作系统不存在一样，因此没有标准输入、没有文件系统，也没有网络。同样，也没有内存分配器，因此像`Box`、`Vec`和`HashMap`这样的类型也无法找到。

在`core`之上是`alloc`，它包含所有依赖于动态内存分配的功能，如集合、智能指针和动态分配的字符串（`String`）。我们将在下一节中回到`alloc`。

大多数情况下，因为`std`重新导出了`core`和`alloc`中的所有内容，开发者不需要了解这三个库之间的差异。这意味着，尽管`Option`技术上存在于`core::option::Option`中，但你可以通过`std::option::Option`来访问它。

然而，在像嵌入式设备这样的非常规环境中，情况就大不相同，因为这类设备没有操作系统，这种区分就变得至关重要。虽然使用 `Iterator` 或对数字列表进行排序是可以的，但嵌入式设备可能根本没有任何有效的方式来访问文件（因为这需要文件系统）或输出到终端（因为这需要终端）—因此没有 `File` 或 `println!`。此外，设备的内存可能极其有限，以至于动态内存分配成为了一种你无法承受的奢侈品，因此任何在运行时分配内存的操作都是不可行的—告别 `Box` 和 `Vec`。

为了避免强迫开发人员在这类环境中小心避开那些基本构造，Rust 提供了一种方法，使得开发者可以选择退出除语言核心功能之外的所有内容：`#![no_std]` 属性。这是一个 crate 级别的属性（`#!`），它将 crate 的预定义（参见第 213 页的框）从 `std::prelude` 切换到 `core::prelude`，从而避免你无意间依赖 `core` 以外的任何在目标环境中可能无法正常工作的内容。

然而，`#![no_std]` 属性的作用仅仅是*全部*—它并不会阻止你通过 `extern std` 显式引入标准库。这可能让人感到意外，因为这意味着标记为 `#![no_std]` 的 crate 实际上可能与不支持 `std` 的目标环境不兼容，但这一设计决定是有意为之：它允许你将 crate 标记为 `no_std` 兼容，但在启用某些特性时仍然可以使用标准库中的功能。例如，许多 crate 有一个名为 `std` 的特性，当启用时，可以访问更复杂的 API，并与 `std` 中的类型进行集成。这使得 crate 的作者可以为受限的使用场景提供核心实现，并为更标准平台上的用户添加附加功能。

## 动态内存分配

正如我们在第一章中讨论的，计算机有许多不同的内存区域，每个区域都有不同的用途。程序代码和静态变量占用静态内存，函数局部变量和函数参数则使用栈内存，堆内存则用于，嗯，其他所有内容。堆支持在运行时分配可变大小的内存区域，这些分配会持续存在，直到你不再需要它们为止。这使得堆内存极为灵活，因此你会在各个地方看到它的使用。`Vec`、`String`、`Arc` 和 `Rc` 以及集合类型都在堆内存中实现，这使得它们可以随着时间的推移而增长或缩小，并且能够从函数中返回而不会被借用检查器抱怨。

在幕后，堆实际上只是一个由*分配器*管理的大块连续内存。正是分配器提供了堆中不同分配的假象，确保这些分配不重叠，并且不再使用的内存区域能够被重用。默认情况下，Rust 使用系统分配器，通常这是由标准 C 库规定的分配器。这适用于大多数用例，但如果有需要，你可以通过`GlobalAlloc`特性和`#[global_allocator]`属性来覆盖 Rust 使用的分配器，这要求实现一个`alloc`方法来分配新内存段，以及`dealloc`方法来将过去的分配返回给分配器进行重用。

在没有操作系统的环境中，标准 C 库通常也不可用，因此标准系统分配器也不可用。由于这个原因，`#![no_std]`也排除了所有依赖于动态内存分配的类型。但由于完全可以在没有完整操作系统的情况下实现内存分配器，Rust 允许你仅选择需要分配器的 Rust 标准库部分，而不需要通过`alloc`包选择所有的`std`。`alloc`包随标准 Rust 工具链一起提供（就像`core`和`std`一样），包含了你最喜欢的堆分配类型，如`Box`、`Arc`、`String`、`Vec`和`BTreeMap`。`HashMap`不在其中，因为它依赖于随机数生成来进行键值哈希，这需要操作系统的支持。要在`no_std`环境中使用`alloc`中的类型，你只需将之前引入`use std::`的代码替换为`use alloc::`即可。不过，请记住，依赖于`alloc`意味着你的`#![no_std]`包将不再可供任何禁止动态内存分配的程序使用，不论是因为它没有分配器，还是因为内存不足以进行动态内存分配。

你可能会觉得奇怪，居然可以编写仅使用 `core` 的非平凡 crate。毕竟，它们不能使用集合、`String` 类型、网络或文件系统，甚至没有时间的概念！`core` 仅 crate 的诀窍在于利用栈和静态分配。例如，对于一个无堆向量，你提前分配足够的内存——无论是在静态内存中还是在函数的栈帧中——用于你预期该向量能够容纳的最大元素数量，然后通过一个 `usize` 来追踪它当前持有的元素数量。要向向量中推送元素，你只需写入（静态大小的）数组中的下一个元素，并递增一个变量以跟踪元素数量。如果向量的长度达到了静态大小，下一次推送将会失败。列表 12-1 给出了一个使用 `const` 泛型实现的无堆向量类型的示例。

```
struct ArrayVec<T, const N: usize> {
    values: [Option<T>; N],
    len: usize,
}
impl<T, const N: usize> ArrayVec<T, N> {
    fn try_push(&mut self, t: T) -> Result<(), T> {
        if self.len == N {
            return Err(t);
        }
        self.values[self.len] = Some(t);
        self.len += 1;
        return Ok(());
    }
}
```

列表 12-1：一个无堆向量类型

我们将 `ArrayVec` 泛型化，既包含元素类型 `T`，也包含最大元素数量 `N`，然后将向量表示为一个包含 `N` 个 *可选* `T` 的数组。该结构始终存储 `N` 个 `Option<T>`，因此它的大小在编译时已知，可以存储在栈上，但它仍然可以像向量一样，通过使用运行时信息来指导我们如何访问该数组。

## Rust 运行时

你可能听说过 Rust 没有运行时的说法。虽然从高层来说这是真的——它没有垃圾回收器、解释器或内置的用户级调度器——但从严格意义上说这并不完全正确。具体来说，Rust 确实有一些特殊代码，在你的 `main` 函数之前运行，并在你的代码中响应某些特殊条件，这实际上是一种最简化的运行时形式。

### 恐慌处理器

这种特殊代码的第一部分是 Rust 的 *恐慌处理器*。当 Rust 代码通过调用 `panic!` 或 `panic_any` 触发恐慌时，恐慌处理器决定接下来发生的事情。当 Rust 运行时可用时——如大多数提供 `std` 的目标——恐慌处理器首先调用通过 `std::panic::set_hook` 设置的 *恐慌钩子*，该钩子默认会向标准错误打印一条消息并可选择性地打印回溯。然后，它会根据当前编译选项（通过 Cargo 配置或直接传递给 `rustc` 的参数）决定是展开当前线程的堆栈，还是终止进程。

然而，并非所有目标平台都提供 panic 处理程序。例如，大多数嵌入式目标平台并不提供，因为针对所有用途的目标平台并没有一个通用的实现方式。对于那些不提供 panic 处理程序的目标平台，Rust 仍然需要知道在发生 panic 时该如何处理。为此，我们可以使用 `#[panic_handler]` 属性来装饰程序中一个符合签名 `fn(&PanicInfo) -> !` 的函数。每当程序触发 panic 时，该函数会被调用，并且会传递一个 `core::panic::PanicInfo` 类型的 panic 信息。函数如何处理这些信息完全没有规定，但它永远不能返回（这由 `!` 返回类型表示）。这一点非常重要，因为 Rust 编译器假定 panic 后的代码永远不会被执行。

panic 处理程序有很多有效的方式来避免返回。标准的 panic 处理程序会展开线程的栈，然后终止该线程，但 panic 处理程序也可以使用 `loop {}` 来停止线程、终止程序，或者做任何其他适合目标平台的操作，甚至是重置设备。

### 程序初始化

与普遍的看法相反，`main` 函数并不是 Rust 程序中首先运行的部分。实际上，在 Rust 二进制文件中，`main` 符号指向的是标准库中名为 `lang_start` 的函数。该函数执行（相对简单的）Rust 运行时的初始化工作，包括将程序的命令行参数存储在 `std::env::args` 可以访问的地方、设置主线程的名称、处理 `main` 函数中的 panic、在程序退出时刷新标准输出以及设置信号处理器。`lang_start` 函数随后会调用你在 crate 中定义的 `main` 函数，这样你就不需要考虑如何处理例如 Windows 和 Linux 在传递命令行参数时的差异了。

这种安排在所有这些设置合理且受支持的平台上运作良好，但在一些嵌入式平台上会遇到问题，因为程序启动时主内存可能无法访问。在这种平台上，你通常需要完全跳过 Rust 的初始化代码，使用 `#![no_main]` crate 级别属性。这个属性会完全跳过 `lang_start`，意味着作为开发者的你必须弄清楚如何启动程序，例如通过声明一个使用 `#[export_name = "main"]` 的函数来匹配目标平台预期的启动序列。

### 内存不足处理程序

如果你编写的程序希望使用 `alloc`，但它是为没有提供分配器的平台构建的，那么你必须通过本章前面提到的 `#[global_allocator]` 属性来指定使用哪个分配器。但你还必须指定如果该全局分配器无法分配内存时该怎么办。具体来说，你需要定义一个*内存不足处理程序*，说明当像 `Vec::push` 这样的不可失败操作需要分配更多内存，但分配器无法提供时应该发生什么。

在启用 `std` 的平台上，内存不足处理程序的默认行为是向标准错误输出打印错误信息，然后中止进程。然而，在一个例如没有标准错误的平台上，显然这不起作用。撰写本文时，在这种平台上，你的程序必须显式地使用不稳定属性 `#[lang = "oom"]` 来定义内存不足处理程序。请记住，处理程序几乎肯定应该阻止后续执行，否则尝试分配的代码将在不知道未能分配所需内存的情况下继续执行！

## 低级内存访问

在第十章中，我们讨论了编译器在将程序语句转换为机器指令时所拥有的相当自由度，以及 CPU 允许执行无序指令的空间。通常，编译器和 CPU 所能利用的快捷方式和优化对程序的语义是不可见的——你通常无法判断，例如，两个读取操作是否相对重排过，或者从同一内存位置的两次读取是否实际上会导致两条 CPU 加载指令。这是经过设计的。语言和硬件设计者仔细指定了程序运行时程序员通常期望的语义，这样你的代码通常会按你预期的方式执行。

然而，`no_std` 编程有时会让你超越“隐形优化”的常规边界。特别是，你经常需要通过*内存映射*与硬件设备进行通信，在这种方式下，设备的内部状态会在内存中的特定区域提供。例如，当你的计算机启动时，内存地址范围 `0xA0000`–`0xBFFFF` 映射到一个粗略的图形渲染管道；在该范围内对单个字节的写入将改变屏幕上的特定像素（或者块，取决于模式）。

当你与设备映射内存交互时，设备可能会对每次内存访问实现自定义行为，因此你 CPU 和编译器对常规内存加载和存储的假设可能不再成立。例如，硬件设备常常有内存映射寄存器，在读取时会被修改，这意味着读取操作会有副作用。在这种情况下，如果你连续两次读取相同的内存地址，编译器就不能安全地省略内存存储操作！

当程序执行突然偏离代码中所表示的方式时，就会出现类似的问题，编译器无法预见这些情况。执行可能会被转移，如果没有底层操作系统来处理处理器异常或中断，或者如果进程收到中断执行的信号。在这些情况下，活动代码段的执行会停止，CPU 开始执行触发偏移的事件处理程序中的指令。通常，由于编译器可以预见所有可能的执行情况，它会安排优化，以使执行无法观察到操作是否已按顺序执行或被优化掉。然而，由于编译器无法预测这些异常跳转，它也无法为这些跳转做出计划以忽视其优化，因此这些事件处理程序可能会观察到与原始程序代码中不同顺序执行的指令。

为了应对这些异常情况，Rust 提供了*volatile*内存操作，这些操作不能与其他 volatile 操作进行省略或重新排序。这些操作以`std::ptr::read_volatile`和`std::ptr::write_volatile`的形式出现。Volatile 操作非常适合访问内存映射的硬件资源：它们直接映射到内存访问操作，没有编译器的伎俩，并且 volatile 操作之间不会重新排序的保证确保即使它们通常看起来可以互换（例如加载一个地址并将数据存储到另一个地址），硬件操作也不会发生顺序错乱。无重新排序的保证也有助于异常执行情况，只要任何触及在异常上下文中访问的内存的代码仅使用 volatile 内存操作。

## 防滥用硬件抽象

Rust 的类型系统擅长将不安全、复杂以及其他不愉快的代码封装在安全、符合人体工学的接口背后。没有比在低级系统编程这个著名复杂的领域中更为重要，那里充满了从晦涩的手册中提取出来的硬件定义的神秘值，以及使用神秘的未文档化汇编指令咒语来让设备达到恰到好处的状态。而这一切发生在一个运行时错误可能不仅仅会崩溃用户程序的空间中！

在`no_std`程序中，使用类型系统来使非法状态无法表示是极其重要的，正如我们在第三章中讨论的那样。如果某些寄存器值的组合不能同时发生，那么可以创建一个单一类型，其类型参数表示相关寄存器的当前状态，并仅在其上实现合法的转换，就像我们在 Listing 3-2 中为火箭示例所做的那样。

例如，考虑一对寄存器，在任何给定时刻最多只有一个寄存器应该是“开启”状态。清单 12-2 展示了如何在一个（单线程）程序中以一种方式表示这一点，使得不可能编写违反该不变式的代码。

```
// raw register address -- private submodule
mod registers;
pub struct On;
pub struct Off;
pub struct Pair<R1, R2>(PhantomData<(R1, R2)>);
impl Pair<Off, Off> {
    pub fn get() -> Option<Self> {
 static mut PAIR_TAKEN: bool = false;
        if unsafe { PAIR_TAKEN } {
            None
        } else {
 // Ensure initial state is correct.
            registers::off("r1");
            registers::off("r2");
            unsafe { PAIR_TAKEN = true };
            Some(Pair(PhantomData))
        }
    }

    pub fn first_on(self) -> Pair<On, Off> {
        registers::set_on("r1");
        Pair(PhantomData)
    }
 // .. and inverse for -> Pair<Off, On>
}
impl Pair<On, Off> {
    pub fn off(self) -> Pair<Off, Off> {
        registers::set_off("r1");
        Pair(PhantomData)
    }
}
// .. and inverse for Pair<Off, On>
```

清单 12-2：静态确保正确操作

这段代码中有一些值得注意的模式。第一个是我们通过在唯一构造函数中检查一个私有的静态布尔值，确保`Pair`类的唯一实例只会存在一次，并使所有方法消耗`self`。接着，我们确保初始状态有效，并且只允许有效的状态转换，因此不变式必须在全局范围内保持成立。

清单 12-2 中的第二个值得注意的模式是我们使用`PhantomData`来利用零大小类型，并以静态方式表示运行时信息。也就是说，在代码的任何给定时刻，类型告诉我们运行时状态*必须*是什么，因此我们不需要在运行时跟踪或检查与寄存器相关的任何状态。当我们需要启用`r1`时，不需要检查`r2`是否已经处于开启状态，因为类型已经防止了编写出现这种情况的程序。

## 交叉编译

通常，你会在一台运行完整操作系统并配备现代硬件的计算机上编写`no_std`程序，但最终会在一个只有 93/4 位 RAM、CPU 像袜子一样的简陋硬件设备上运行。这就需要*交叉编译*——你需要在开发环境中编译代码，但需要为袜子编译。这并不是交叉编译唯一重要的场景。例如，现在越来越常见的是，构建流水线生成所有消费者平台的二进制文件，而不是为每个消费者可能使用的平台创建一个构建流水线，这就需要使用交叉编译。

交叉编译涉及两个平台：*宿主*平台和*目标*平台。宿主平台是进行编译的平台，目标平台是最终运行编译输出的平台。我们通过*目标三元组*来指定平台，形式为`machine-vendor-os`。`machine`部分决定了代码将运行的机器架构，如`x86_64`、`armv7`或`wasm32`，并告诉编译器使用哪种指令集来生成机器代码。`vendor`部分通常在 Windows 上为`pc`，在 macOS 和 iOS 上为`apple`，在其他地方为`unknown`，且不会在编译过程中产生有意义的影响；它通常不重要，甚至可以省略。`os`部分告诉编译器最终的二进制文件应使用何种格式，所以`linux`表示 Linux 的*.so*文件，`windows`表示 Windows 的*.dll*文件，依此类推。

要告诉 Cargo 进行交叉编译，你只需传递 `--target <``target triple``>` 参数，指定你选择的三元组。然后，Cargo 会将这个信息转发给 Rust 编译器，以便生成适用于给定目标平台的二进制文件。Cargo 还会确保使用适用于该平台的标准库版本——毕竟，标准库包含了许多条件编译指令（使用 `#[cfg(...)]`），以便调用正确的系统调用并使用适合架构的实现，因此我们不能在目标平台上使用主机平台的标准库。

目标平台还决定了标准库中可用的组件。例如，`x86_64-unknown-linux-gnu` 包含完整的 `std` 库，而像 `thumbv7m-none-eabi` 这样的目标平台没有，并且甚至没有定义分配器，因此如果你在没有显式定义分配器的情况下使用 `alloc`，你将会遇到构建错误。这对于测试你编写的代码是否*确实*不需要 `std` 很有用（记住，即使使用 `#![no_std]`，你仍然可以使用 `use std::`，因为 `no_std` 只是放弃了 `std` 的预导入）。如果你让持续集成管道在 `--target thumbv7m-none-eabi` 的条件下构建你的 crate，那么任何试图访问 `core` 以外组件的行为都会触发构建失败。关键是，这也会检查你的 crate 是否不小心引入了依赖项，而这些依赖项本身使用了 `std`（或 `alloc`）中的项目。

## 总结

在本章中，我们讨论了标准库的底层内容——更准确地说，是 `std` 之下的内容。我们讲解了使用 `core` 可以获得的内容，如何通过 `alloc` 扩展非 `std` 的使用范围，以及 (非常小的) Rust 运行时为你的程序添加了什么，使得 `fn main` 能够工作。我们还探讨了如何与设备映射内存交互，以及如何处理在硬件编程的最低层次可能发生的非传统执行模式，并且如何在 Rust 类型系统中安全地封装硬件的奇特之处。接下来，我们将从非常小的内容转向非常大的内容，讨论如何在 Rust 生态系统中导航、理解，甚至可能为其做出贡献。
