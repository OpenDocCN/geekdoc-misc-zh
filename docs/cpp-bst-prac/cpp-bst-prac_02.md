# 利用现有工具

# 利用现有工具

在开发过程中应尽早建立一个自动化框架来执行这些工具。检出源代码、构建和执行测试不应该超过 2-3 个命令。一旦测试执行完成，你应该几乎完整地了解代码的状态和质量。

## 源代码控制

对于任何软件开发项目，源代码控制是绝对必要的。如果你还没有使用，请开始使用。

+   [GitHub](https://github.com/) - 允许无限公共仓库，但必须付费使用私有仓库。

+   [Bitbucket](https://bitbucket.org/) - 允许免费拥有无限私有仓库，最多可有 5 位协作者。

+   [SourceForge](http://sourceforge.net/) - 仅限开源托管。

+   [GitLab](https://gitlab.com/) - 允许无限公共和私有仓库，免费包含无限 CI 运行器。

+   [Visual Studio Online](https://visualstudio.com) ([`www.visualstudio.com/what-is-visual-studio-online-vs`](http://www.visualstudio.com/what-is-visual-studio-online-vs)) - 允许无限公共仓库，但必须付费使用私有仓库。仓库可以是 git 或 TFVC。此外：问题跟踪、项目计划（多种敏捷模板，如 SCRUM）、集成的托管构建，将所有这些集成到 Microsoft Visual Studio 中。仅限 Windows。

## 构建工具

使用行业标准的广泛接受的构建工具。这可以防止你在发现 / 链接新库 / 打包产品 / 等时重复造轮子。例如：

+   [CMake](http://www.cmake.org/)

    +   考虑使用 [`github.com/sakra/cotire/`](https://github.com/sakra/cotire/) 以提升构建性能

    +   考虑使用 [`github.com/toeb/cmakepp`](https://github.com/toeb/cmakepp) 以增强可用性

    +   利用 [`cmake.org/cmake/help/v3.6/command/target_compile_features.html`](https://cmake.org/cmake/help/v3.6/command/target_compile_features.html) 中的 C++ 标准标志

+   [Conan](https://www.conan.io/) - 用于 C++ 的跨平台依赖管理器

+   [C++ Archive Network (CPPAN)](https://cppan.org/) - 用于 C++ 的跨平台依赖管理器

+   [Waf](https://waf.io/)

+   [FASTBuild](http://www.fastbuild.org/)

+   [Ninja](https://ninja-build.org/) - 可大大提高较大项目的增量构建时间。可用作 CMake 的目标。

+   [Bazel](http://bazel.io/) - 注意：仅适用于 MacOS 和 Linux。

+   [gyp](https://chromium.googlesource.com/external/gyp/) - Google 的用于 Chromium 的构建工具。

+   [maiken](https://github.com/Dekken/maiken) - 具有类似 Maven 配置风格的跨平台构建工具。

+   [Qt Build Suite](http://doc.qt.io/qbs/) - 来自 Qt 的跨平台构建工具。

+   [meson](http://mesonbuild.com/index.html) - 旨在尽可能快速和用户友好的开源构建系统。

+   [premake](https://premake.github.io/)

记住，这不仅是一个构建工具，还是一种编程语言。尽量保持良好的干净构建脚本，并遵循您使用的工具的推荐实践。

## 持续集成

一旦选择了构建工具，请设置持续集成环境。

持续集成（CI）工具会在更改被推送到存储库时自动构建源代码。这些可以私下托管或使用 CI 主机托管。

+   [Travis CI](http://travis-ci.org)

    +   与 C++配合良好。

    +   专为与 GitHub 一起使用而设计。

    +   在 GitHub 上的公共存储库免费。

+   [AppVeyor](http://www.appveyor.com/)

    +   支持 Windows、MSVC 和 MinGW。

    +   在 GitHub 上的公共存储库免费。

+   [Hudson CI](http://hudson-ci.org/) / [Jenkins CI](https://jenkins-ci.org/)

    +   需要 Java 应用服务器。

    +   支持 Windows、OS X 和 Linux。

    +   可以通过许多插件进行扩展。

+   [TeamCity](https://www.jetbrains.com/teamcity)

    +   对于开源项目有免费选项。

+   [Decent CI](https://github.com/lefticus/decent_ci)

    +   简单的即席持续集成，将结果发布到 GitHub。

    +   支持 Windows、OS X 和 Linux。

    +   被[ChaiScript](http://chaiscript.com/ChaiScript-BuildResults/full_dashboard.html)使用。

+   [Visual Studio Online](https://visualstudio.com) ([`www.visualstudio.com/what-is-visual-studio-online-vs`](http://www.visualstudio.com/what-is-visual-studio-online-vs))

    +   与 Visual Studio Online 的源代码存储库紧密集成。

    +   使用 MSBuild（Visual Studio 的构建引擎），可在 Windows、OS X 和 Linux 上使用。

    +   提供托管构建代理，也允许用户提供构建代理。

    +   可以从 Microsoft Visual Studio 内部进行控制和监视。

    +   通过 Microsoft Team Foundation Server 进行本地安装。

+   [GitLab](https://gitlab.com)

    +   使用自定义的 Docker 镜像，因此可以用于 C++。

    +   具有免费的共享运行器。

    +   具有对覆盖率分析结果的轻松处理。

如果您在 GitHub 上拥有一个开源的公共托管项目：

+   立即启用 Travis Ci 和 AppVeyor 集成。我们会等你回来。有关如何为基于 CMake 的 C++应用程序启用它的简单示例，请参见此处：[`github.com/ChaiScript/ChaiScript/blob/master/.travis.yml`](https://github.com/ChaiScript/ChaiScript/blob/master/.travis.yml)

+   启用下面列出的覆盖率工具之一（Codecov 或 Coveralls）。

+   启用[Coverity Scan](https://scan.coverity.com)

这些工具都是免费的，并且相对容易设置。一旦设置好，您将获得项目的持续构建、测试、分析和报告。免费的。

## 编译器

使用每个可用且合理的警告选项。一些警告选项仅在启用了优化时才有效，或者在选择的优化级别越高时效果越好，例如使用 GCC 的[`-Wnull-dereference`](https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html#index-Wnull-dereference-367)。

您应该尽可能多地使用各种编译器来编译您的平台。每个编译器都会稍微不同地实现标准，并支持多个编译器将有助于确保最具可移植性、最可靠的代码。

### GCC / Clang

`-Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic`

+   `-Wall -Wextra` 合理且标准

+   `-Wshadow` 如果变量声明遮蔽了父上下文中的变量声明，则向用户发出警告

+   `-Wnon-virtual-dtor` 如果具有虚函数的类具有非虚析构函数，则向用户发出警告。这有助于捕获难以跟踪的内存错误

+   `-Wold-style-cast` 对 c 风格转换发出警告

+   `-Wcast-align` 警告潜在性能问题的转换

+   `-Wunused` 警告任何未使用的内容

+   `-Woverloaded-virtual` 如果您重载（而不是覆盖）虚函数，则发出警告

+   `-Wpedantic` 如果使用非标准 C++，则发出警告

+   `-Wconversion` 警告可能会丢失数据的类型转换

+   `-Wsign-conversion` 警告有符号转换

+   `-Wmisleading-indentation` 如果缩进暗示存在块但实际不存在块，则发出警告

+   `-Wduplicated-cond` 如果`if` / `else`链具有重复条件，则发出警告

+   `-Wduplicated-branches` 如果`if` / `else`分支具有重复代码，则发出警告

+   `-Wlogical-op` 警告逻辑操作被用于可能需要位操作的地方

+   `-Wnull-dereference` 如果检测到空指针解引用，则发出警告

+   `-Wuseless-cast` 如果执行与相同类型的转换，则发出警告

+   `-Wdouble-promotion` 如果`float`被隐式提升为`double`，则发出警告

+   `-Wformat=2` 在围绕格式化输出的函数（即`printf`）存在安全问题时发出警告

考虑在 Clang 上使用`-Weverything`，并禁用您需要的少数警告

`-Weffc++` 警告模式可能会太吵，但如果适用于您的项目，请使用它。

### MSVC

`/W4 /W44640` - 使用这些并考虑以下内容

+   `/W4` 所有合理的警告

+   `/w14242` 'identfier': 从'type1'到'type1'的转换，可能会丢失数据

+   `/w14254` 'operator': 从'type1:field_bits'到'type2:field_bits'的转换，可能会丢失数据

+   `/w14263` 'function': 成员函数未覆盖任何基类虚成员函数

+   `/w14265` 'classname': 类具有虚函数，但析构函数不是虚函数，此类的实例可能无法正确销毁

+   `/w14287` 'operator': 无符号/负常量不匹配

+   `/we4289` 使用了非标准扩展：'variable': 在 for 循环中声明的循环控制变量在 for 循环范围之外使用

+   `/w14296` 'operator': 表达式始终为'boolean_value'

+   `/w14311` 'variable': 从'type1'到'type2'的指针截断

+   `/w14545` 逗号前的表达式求值为缺少参数列表的函数

+   `/w14546` 逗号前的函数调用缺少参数列表

+   `/w14547` 'operator': 逗号前的运算符没有效果；预期具有副作用的运算符

+   `/w14549` 'operator': 逗号前的运算符没有效果；您是否打算使用'operator'？

+   `/w14555` 表达式没有效果；预期具有副作用的表达式

+   `/w14619` pragma 警告：没有警告编号'number'

+   `/w14640` 启用线程不安全的静态成员初始化警告

+   `/w14826` 从'type1'转换为'type_2'是符号扩展的。这可能导致意外的运行时行为。

+   `/w14905` 宽字符串文字转换为'LPSTR'

+   `/w14906` 字符串文字转换为'LPWSTR'

+   `/w14928` 非法的拷贝初始化；隐式应用了多个用户定义的转换

不推荐

+   `/Wall` - 还会对从标准库中包含的文件发出警告，因此它并不是非常有用，而且会产生太多额外的警告。

### 一般

从一开始就使用非常严格的警告设置。在项目进行中尝试提高警告级别可能会很痛苦。

考虑使用*将警告视为错误*设置。在 MSVC 中为`/Wx`，在 GCC / Clang 中为`-Werror`

## 基于 LLVM 的工具

基于 LLVM 的工具最适合与能够输出编译命令数据库的构建系统（例如 cmake）一起使用，例如：

```
$ cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON . 
```

如果您没有使用这样的构建系统，可以考虑使用[Build EAR](https://github.com/rizsotto/Bear)，它将连接到您的构建系统并为您生成编译命令数据库。

CMake 现在也具有在[普通编译](https://cmake.org/cmake/help/latest/prop_tgt/LANG_CLANG_TIDY.html)过程中调用`clang-tidy`的内置支持。

+   [include-what-you-use](https://github.com/include-what-you-use)，[示例结果](https://github.com/ChaiScript/ChaiScript/commit/c0bf6ee99dac14a19530179874f6c95255fde173)

+   [clang-modernize](http://clang.llvm.org/extra/clang-modernize.html)，[示例结果](https://github.com/ChaiScript/ChaiScript/commit/6eab8ddfe154a4ebbe956a5165b390ee700fae1b)

+   [clang-check](http://clang.llvm.org/docs/ClangCheck.html)

+   [clang-tidy](http://clang.llvm.org/extra/clang-tidy.html)

## 静态分析器

最佳选择是作为自动化构建系统的一部分运行的静态分析器。Cppcheck 和 clang 满足免费选项的要求。

### Coverity 扫描

[Coverity](https://scan.coverity.com/) 有一个免费的（针对开源）静态分析工具包，可以与[Travis CI](http://travis-ci.org)和[AppVeyor](http://www.appveyor.com/)集成，在每次提交时都可以工作。

### PVS-Studio

[PVS-Studio](http://www.viva64.com/en/pvs-studio/) 是一个用于检测 C、C++和 C#程序源代码中 bug 的工具。对于个人学术项目、开源非商业项目和个人开发者的独立项目，它是免费的。它在 Windows 和 Linux 环境下工作。

### Cppcheck

[Cppcheck](http://cppcheck.sourceforge.net/) 是免费开源的。它力求达到 0 个假阳性，并且做得很好。因此，应该启用所有警告：`--enable=all`

注：

+   为了正确工作，需要为头文件提供格式良好的路径，因此在使用之前不要忘记传递：`--check-config`。

+   发现未使用的头文件不适用于`-j`大于 1。

+   记得为带有大量`#ifdef`的代码添加`--force`以检查所有`#ifdef`。

### Clang 的静态分析器

clang 分析器的默认选项适用于各自的平台。它可以直接从[CMake](http://garykramlich.blogspot.com/2011/10/using-scan-build-from-clang-with-cmake.html)使用。它们也可以通过 clang-check 和 clang-tidy 从基于 LLVM 的工具中调用。

此外，[CodeChecker](https://github.com/Ericsson/CodeChecker)可作为 clang 静态分析的前端。

`clang-tidy`可以通过[Clang Power Tools](https://caphyon.github.io/clang-power-tools/)扩展轻松与 Visual Studio 集成。

### MSVC 的静态分析器

可通过`/analyze` [命令行选项](http://msdn.microsoft.com/en-us/library/ms173498.aspx)启用。暂时我们将坚持使用默认选项。

### Flint / Flint++

[Flint](https://github.com/facebook/flint)和[Flint++](https://github.com/L2Program/FlintPlusPlus)是根据 Facebook 的编码标准分析 C++代码的 linters。

### ReSharper C++ / CLion

来自[JetBrains](https://www.jetbrains.com/cpp/)的这两个工具提供了一定程度的静态分析和常见问题的自动修复。他们为开源项目领导者提供了免费许可证选项。

### Cevelop

基于 Eclipse 的[Cevelop](https://www.cevelop.com/) IDE 提供了各种静态分析和重构/代码修复工具。例如，您可以用 C++ `constexprs`替换宏，重构命名空间（提取/内联`using`，限定名称），并将您的代码重构为 C++11 的统一初始化语法。Cevelop 可免费使用。

### Qt Creator

Qt Creator 可以插入 clang 静态分析器。

## 运行时检查器

### 代码覆盖率分析

在执行测试时应运行覆盖分析工具，以确保整个应用程序都被测试到。不幸的是，覆盖分析需要禁用编译器优化。这可能导致测试执行时间显着增加。

+   [Codecov](https://codecov.io/)

    +   集成了 Travis CI 和 AppVeyor

    +   适用于开源项目的免费版

+   [Coveralls](https://coveralls.io/)

    +   集成了 Travis CI 和 AppVeyor

    +   适用于开源项目的免费版

+   [LCOV](http://ltp.sourceforge.net/coverage/lcov.php)

    +   高度可配置

+   [Gcovr](http://gcovr.com/)

+   [kcov](http://simonkagstrom.github.io/kcov/index.html)

    +   与 codecov 和 coveralls 集成

    +   无需特殊的编译器标志即可执行代码覆盖率报告，只需插装调试符号。

### Valgrind

[Valgrind](http://www.valgrind.org/)是一个运行时代码分析器，可以检测内存泄漏、竞争条件和其他相关问题。它支持各种 Unix 平台。

### Dr Memory

类似于 Valgrind。[`www.drmemory.org`](http://www.drmemory.org)

### GCC / Clang 分析器

这些工具提供了许多与 Valgrind 相同的功能，但内置于编译器中。它们易于使用，并提供了出错的报告。

+   地址分析器

+   内存分析器

+   线程分析器

+   未定义行为分析器

### 模糊分析器

如果您的项目接受用户定义的输入，请考虑运行模糊输入测试器。

这两个工具都使用覆盖报告来找到新的代码执行路径，并尝试为您的代码繁衍出新的输入。它们可以找到崩溃、挂起和您不知道被视为有效的输入。

+   [美国模糊跳跃](http://lcamtuf.coredump.cx/afl/)

+   [LibFuzzer](http://llvm.org/docs/LibFuzzer.html)

+   [KLEE](http://klee.github.io/) - 可用于模糊测试单个函数

## 忽略警告

如果团队一致认为编译器或分析器在警告某些不正确或不可避免的内容，则团队将尽可能地在代码的局部部分禁用特定错误。

确保在禁用代码部分后重新启用警告。您不希望禁用的警告泄漏到其他代码中。

## 测试

如上所述，CMake 具有用于执行测试的内置框架。确保您使用的任何构建系统都具有内置的执行测试的方法。

为了进一步帮助执行测试，请考虑使用诸如[Google Test](https://github.com/google/googletest)、[Catch](https://github.com/philsquared/Catch)、[CppUTest](https://github.com/cpputest/cpputest)或[Boost.Test](http://www.boost.org/doc/libs/release/libs/test/)之类的库来帮助您组织测试。

### 单元测试

单元测试是针对小块代码、可独立测试的单个函数。

### 集成测试

每个提交的功能或错误修复都应启用一个测试。另请参阅代码覆盖分析。这些测试比单元测试更高级。它们仍然应该在个别特性的范围内限制。

### 负面测试

不要忘记确保您的错误处理被测试并正常工作。如果您的目标是实现 100%的代码覆盖率，这将变得很明显。

## 调试

### uftrace

[uftrace](https://github.com/namhyung/uftrace) 可用于生成程序执行的函数调用图

### rr

[rr](http://rr-project.org/) 是一个支持 C++ 的免费（开源）反向调试器。

## 其他工具

### Metrix++

[Metrix++](http://metrixplusplus.sourceforge.net/) 可以识别并报告代码中最复杂的部分。减少复杂代码有助于您和编译器更好地理解它并进行优化。

### ABI 兼容性检查器

[ABI 兼容性检查器](http://ispras.linuxbase.org/index.php/ABI_compliance_checker) (ACC) 可以分析两个库版本，并生成有关 API 和 C++ ABI 更改的详细兼容性报告。这可以帮助库开发人员发现无意中的破坏性更改，以确保向后兼容性。

### CNCC

[可定制的命名约定检查器](https://github.com/mapbox/cncc) 可以报告代码中不遵循某些命名约定的标识符。

### ClangFormat

[ClangFormat](http://clang.llvm.org/docs/ClangFormat.html) 能够自动检查和纠正代码格式，使其符合组织的约定。[多部分系列](https://engineering.mongodb.com/post/succeeding-with-clangformat-part-1-pitfalls-and-planning/) 关于利用 clang-format。

### SourceMeter

[SourceMeter](https://www.sourcemeter.com/) 提供免费版本，为您的代码提供许多不同的度量标准，还可以调用 cppcheck。

### Bloaty McBloatface

[Bloaty McBloatface](https://github.com/google/bloaty) 是用于类 Unix 平台的二进制大小分析器/分析工具
