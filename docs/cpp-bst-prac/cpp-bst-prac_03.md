# 风格

# 风格

一致性是风格的最重要方面。第二重要的方面是遵循普通 C++ 程序员习惯阅读的风格。

C++ 允许任意长度的标识符名称，因此在命名时没有必要使用简略的方式。使用描述性的名称，并在风格上保持一致。

+   内联代码（`CamelCase`）不需要翻译。

+   内联代码（`snake_case`）不需要翻译。

是常见的例子。*snake_case* 具有一个优点，即如果需要，它也可以与拼写检查器一起使用。

## 建立一个风格指南

无论您建立什么样的风格指南，都要确保实现一个指定您期望的风格的 `.clang-format` 文件。虽然这不能帮助命名，但对于一个开源项目来说，保持一致的风格尤为重要。

每个 IDE 和许多编辑器都内置了对 clang-format 的支持，或者可以通过插件轻松安装。

+   VSCode [`marketplace.visualstudio.com/items?itemName=xaver.clang-format`](https://marketplace.visualstudio.com/items?itemName=xaver.clang-format)

+   VisualStudio [`marketplace.visualstudio.com/items?itemName=LLVMExtensions.ClangFormat#review-details`](https://marketplace.visualstudio.com/items?itemName=LLVMExtensions.ClangFormat#review-details)

+   Resharper++：[`www.jetbrains.com/help/resharper/2017.2/Using_Clang_Format.html`](https://www.jetbrains.com/help/resharper/2017.2/Using_Clang_Format.html)

+   Vim

    +   [`github.com/rhysd/vim-clang-format`](https://github.com/rhysd/vim-clang-format)

    +   [`github.com/chiel92/vim-autoformat`](https://github.com/chiel92/vim-autoformat)

+   XCode：[`github.com/travisjeffery/ClangFormat-Xcode`](https://github.com/travisjeffery/ClangFormat-Xcode)

## 常见的 C++ 命名约定

+   类型以大写字母开头：`MyClass`。

+   函数和变量以小写字母开头：`myMethod`。

+   常量全部大写：`const double PI=3.14159265358979323;`。

C++ 标准库（以及其他知名的 C++ 库，如 [Boost](http://www.boost.org/)）使用这些指南：

+   宏名称使用大写字母和下划线：`INT_MAX`。

+   模板参数名称使用驼峰式命名：`InputIterator`。

+   所有其他名称都使用蛇形命名：`unordered_map`。

## 区分私有对象数据

使用 `m_` 前缀命名私有数据以区分它们与公共数据。`m_` 代表 "member" 数据。

## 区分函数参数

最重要的是在您的代码库中保持一致性；这是帮助保持一致性的一种可能性。

使用 `t_` 前缀命名函数参数。`t_` 可以被视为 "the"，但含义是任意的。重点是在给我们一个一致的命名策略的同时，将函数参数与作用域中的其他变量区分开来。

您的组织可以选择任何前缀或后缀。这只是一个示例。*这个建议是有争议的，关于这个问题的讨论请参见问题 [#11](https://github.com/lefticus/cppbestpractices/issues/11)。*

```
struct Size
{
  int width;
  int height;

  Size(int t_width, int t_height) : width(t_width), height(t_height) {}
};

// This version might make sense for thread safety or something,
// but more to the point, sometimes we need to hide data, sometimes we don't.
class PrivateSize
{
  public:
    int width() const { return m_width; }
    int height() const { return m_height; }
    PrivateSize(int t_width, int t_height) : m_width(t_width), m_height(t_height) {}

  private:
    int m_width;
    int m_height;
}; 
```

## 不要以 `_` 开头命名任何东西。

如果这样做，您会冒与编译器和标准库实现保留名称发生冲突的风险：

[`stackoverflow.com/questions/228783/what-are-the-rules-about-using-an-underscore-in-a-c-identifier`](http://stackoverflow.com/questions/228783/what-are-the-rules-about-using-an-underscore-in-a-c-identifier)

## 良好的示例

```
class MyClass
{
public:
  MyClass(int t_data)
    : m_data(t_data)
  {
  }

  int getData() const {
    return m_data;
  }

private:
  int m_data;
}; 
```

## 启用源目录外构建

确保生成的文件进入与源文件分离的输出文件夹。

## 使用`nullptr`

C++11 引入了`nullptr`，它是表示空指针的特殊值。应该使用它来代替`0`或`NULL`来表示空指针。

## 注释

注释块应使用`//`而不是`/* */`。使用`//`使得在调试过程中注释掉一块代码变得更容易。

```
// this function does something
int myFunc() {
} 
```

在调试过程中注释掉此函数块我们可能会这样做：

```
/*
// this function does something
int myFunc()
{
}
*/ 
```

如果函数注释头使用了`/* */`，这是不可能的。

## 绝不在头文件中使用`using namespace`

这会导致你`using`的命名空间被拉入包含该头文件的所有文件的命名空间中。这会污染命名空间，并可能导致将来发生名称冲突。在实现文件中写`using namespace`是可以的。

## 包含保护

头文件必须包含一个明确命名的包含保护，以避免多次包含相同的头文件而引发问题，并防止与其他项目的头文件冲突。

```
#ifndef MYPROJECT_MYCLASS_HPP
#define MYPROJECT_MYCLASS_HPP

namespace MyProject {
  class MyClass {
  };
}

#endif 
```

您还可以考虑使用`#pragma once`指令，该指令在许多编译器中都是准标准的。它很简洁，表达意图清晰。

## 大括号`{}`是必需的用于块。

不将它们包含在内可能导致代码中的语义错误。

```
// Bad Idea
// This compiles and does what you want, but can lead to confusing
// errors if modification are made in the future and close attention
// is not paid.
for (int i = 0; i < 15; ++i)
  std::cout << i << std::endl;

// Bad Idea
// The cout is not part of the loop in this case even though it appears to be.
int sum = 0;
for (int i = 0; i < 15; ++i)
  ++sum;
  std::cout << i << std::endl;

// Good Idea
// It's clear which statements are part of the loop (or if block, or whatever).
int sum = 0;
for (int i = 0; i < 15; ++i) {
  ++sum;
  std::cout << i << std::endl;
} 
```

## 保持行的合理长度

```
// Bad Idea
// hard to follow
if (x && y && myFunctionThatReturnsBool() && caseNumber3 && (15 > 12 || 2 < 3)) {
}

// Good Idea
// Logical grouping, easier to read
if (x && y && myFunctionThatReturnsBool()
    && caseNumber3
    && (15 > 12 || 2 < 3)) {
} 
```

许多项目和编码标准有一个软性指南，即应尽量每行使用不超过约 80 或 100 个字符。这样的代码通常更容易阅读。它还可以使得在一个屏幕上同时显示两个单独的文件而无需缩小字体成为可能。

## 使用 "" 包含本地文件

`<>` 保留用于[系统包含](http://blog2.emptycrate.com/content/when-use-include-verses-include)。

```
// Bad Idea. Requires extra -I directives to the compiler
// and goes against standards.
#include <string>
#include <includes/MyHeader.hpp>

// Worse Idea
// Requires potentially even more specific -I directives and
// makes code more difficult to package and distribute.
#include <string>
#include <MyHeader.hpp>

// Good Idea
// Requires no extra params and notifies the user that the file
// is a local file.
#include <string>
#include "MyHeader.hpp" 
```

## 初始化成员变量

...使用成员初始化列表。

对于 POD 类型，使用初始化列表的性能与手动初始化相同，但对于其他类型，存在明显的性能提升，请参见下文。

```
// Bad Idea
class MyClass
{
public:
  MyClass(int t_value)
  {
    m_value = t_value;
  }

private:
  int m_value;
};

// Bad Idea
// This leads to an additional constructor call for m_myOtherClass
// before the assignment.
class MyClass
{
public:
  MyClass(MyOtherClass t_myOtherClass)
  {
    m_myOtherClass = t_myOtherClass;
  }

private:
  MyOtherClass m_myOtherClass;
};

// Good Idea
// There is no performance gain here but the code is cleaner.
class MyClass
{
public:
  MyClass(int t_value)
    : m_value(t_value)
  {
  }

private:
  int m_value;
};

// Good Idea
// The default constructor for m_myOtherClass is never called here, so 
// there is a performance gain if MyOtherClass is not is_trivially_default_constructible. 
class MyClass
{
public:
  MyClass(MyOtherClass t_myOtherClass)
    : m_myOtherClass(t_myOtherClass)
  {
  }

private:
  MyOtherClass m_myOtherClass;
}; 
```

在 C++11 中，您可以为每个成员分配默认值（使用`=`或使用`{}`）。

### 使用`=`分配默认值

```
// ... //
private:
  int m_value = 0; // allowed
  unsigned m_value_2 = -1; // narrowing from signed to unsigned allowed
// ... // 
```

这确保了没有构造函数会“忘记”初始化成员对象。

### 使用大括号初始化分配默认值

使用大括号初始化不允许在编译时发生窄化。

```
// Best Idea

// ... //
private:
  int m_value{ 0 }; // allowed
  unsigned m_value_2 { -1 }; // narrowing from signed to unsigned not allowed, leads to a compile time error
// ... // 
```

除非你有充分的理由，否则优先使用`{}`初始化而不是`=`。

忘记初始化成员是未定义行为错误的源头，往往极其难以发现。

如果成员变量在初始化后不会改变，则标记为`const`。

```
class MyClass
{
public:
  MyClass(int t_value)
    : m_value{t_value}
  {
  }

private:
  const int m_value{0};
}; 
```

由于 const 成员变量不能被赋予新值，因此这样的类可能没有有意义的复制赋值运算符。

## 始终使用命名空间

几乎没有理由在全局命名空间中声明标识符。相反，函数和类应存在于适当命名的命名空间中或存在于命名空间内的类中。将标识符放置在全局命名空间中可能会与其他库（主要是没有命名空间的 C 库）的标识符发生冲突。

## 对于标准库功能，请使用正确的整数类型。

标准库通常对与大小相关的任何内容使用`std::size_t`。`size_t`的大小是由实现定义的。

通常，使用`auto`将避免大多数这些问题，但不是全部。

确保您坚持使用正确的整数类型，并与 C++标准库保持一致。在您当前使用的平台上可能不会发出警告，但在更改平台时可能会发出警告。

*请注意，在对无符号值执行某些操作时可能会导致整数下溢。例如：*

```
std::vector<int> v1{2,3,4,5,6,7,8,9};
std::vector<int> v2{9,8,7,6,5,4,3,2,1};
const auto s1 = v1.size();
const auto s2 = v2.size();
const auto diff = s1 - s2; // diff underflows to a very large number 
```

## 使用.hpp 和.cpp 作为您的文件扩展名。

最终，这是一种偏好问题，但.hpp 和.cpp 在各种编辑器和工具中都得到了广泛认可。因此，选择是实用的。具体来说，Visual Studio 只自动识别.cpp 和.cxx 作为 C++文件，而 Vim 不一定会将.cc 识别为 C++文件。

一个特别大的项目（[OpenStudio](https://github.com/NREL/OpenStudio)）使用.hpp 和.cpp 用于用户生成的文件，.hxx 和.cxx 用于工具生成的文件。两者都得到了良好的认可，并且有区别是有帮助的。

## 不要混合使用制表符和空格。

一些编辑器默认使用制表符和空格的混合进行缩进。这会使代码对于不使用完全相同制表符缩进设置的任何人都无法阅读。配置您的编辑器，以防止这种情况发生。

## 永远不要将具有副作用的代码放在`assert()`中。

```
assert(registerSomeThing()); // make sure that registerSomeThing() returns true 
```

上述代码在进行调试构建时成功，但在进行发布构建时会被编译器删除，从而在调试和发布构建之间产生不同的行为。这是因为`assert()`是一个宏，在发布模式下会扩展为空。

## 不要害怕模板。

它们可以帮助您遵循[DRY 原则](http://en.wikipedia.org/wiki/Don%27t_repeat_yourself)。它们应优先于宏，因为宏不尊重命名空间等。

## 明智地使用运算符重载。

运算符重载的发明是为了实现表达性的语法。在添加两个大整数时，看起来像`a + b`而不是`a.add(b)`。另一个常见示例是`std::string`，在其中使用`string1 + string2`连接两个字符串非常普遍。

但是，如果过度或错误地重载运算符，可能会轻松创建难以阅读的表达式。在重载运算符时，有三条基本规则需要遵循，如[stackoverflow 上](http://stackoverflow.com/questions/4421706/operator-overloading/4421708#4421708)所述。

具体来说，您应该记住以下几点：

+   处理资源时，重载`operator=()`是必须的。参见考虑零规则下面。

+   对于所有其他运算符，只有在通常与这些运算符相关联的情况下重载它们时才重载它们。典型的情况包括使用+连接事物，否定可以被视为“真”或“假”的表达式等。

+   始终注意[运算符优先级](http://en.cppreference.com/w/cpp/language/operator_precedence)，并尝试规避不直观的结构。

+   除非实现数值类型或按照特定领域的公认语法，否则不要重载像~或%这样的奇异运算符。

+   [永远不要](http://stackoverflow.com/questions/5602112/when-to-overload-the-comma-operator?answertab=votes#tab-top)重载`operator,()`（逗号运算符）。

+   处理流时使用非成员函数`operator>>()`和`operator<<()`。例如，你可以重载`operator<<(std::ostream &, MyClass const &)`来使你的类能够“写入”到流中，例如`std::cout`或`std::fstream`或`std::stringstream`。后者通常用于创建值的字符串表示。

+   还有更多常见的运算符可以重载，[在这里描述了](http://stackoverflow.com/questions/4421706/operator-overloading?answertab=votes#tab-top)。

关于自定义运算符的实现细节的更多提示可以在[这里](http://courses.cms.caltech.edu/cs11/material/cpp/donnie/cpp-ops.html)找到。

## 避免隐式转换

### 单参数构造函数

单参数构造函数可以在编译时自动应用以在类型之间进行转换。这对于`std::string(const char *)`之类的事情很方便，但通常应避免使用，因为它们可能会增加意外的运行时开销。

反而将单参数构造函数标记为`explicit`，这需要显式调用它们。

### 转换运算符

与单参数构造函数类似，转换运算符可以被编译器调用并引入意外的开销。它们也应标记为`explicit`。

```
//bad idea
struct S {
  operator int() {
    return 2;
  }
}; 
```

```
//good idea
struct S {
  explicit operator int() {
    return 2;
  }
}; 
```

## 考虑零规则

零规则指出，除非你正在构造的类采用一种新颖的所有权形式，否则不要提供编译器可以提供的任何函数（拷贝构造函数、拷贝赋值操作符、移动构造函数、移动赋值操作符、析构函数）。

目标是让编译器提供最佳版本，在添加更多成员变量时自动维护。

[原始文章](https://rmf.io/cxx11/rule-of-zero)提供了背景，而[后续文章](http://www.nirfriedman.com/2015/06/27/cpp-rule-of-zero/)解释了几乎 100%的实现技术。
