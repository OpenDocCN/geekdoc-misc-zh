# 考虑性能

# 考虑性能

## 构建时间

### 尽可能进行前向声明

这样：

```
// some header file
class MyClass;

void doSomething(const MyClass &); 
```

而不是：

```
// some header file
#include "MyClass.hpp"

void doSomething(const MyClass &); 
```

这也适用于模板：

```
template<typename T> class MyTemplatedType; 
```

这是一种积极的方法来减少编译时间和重新构建依赖项。

### 避免不必要的模板实例化

模板不是免费实例化的。实例化许多模板或比必要更多代码的模板会增加编译后代码的大小和构建时间。

更多示例请参阅[此文章](http://blog2.emptycrate.com/content/template-code-bloat-revisited-smaller-makeshared)。

### 避免递归模板实例化

递归模板实例化可能会给编译器带来显著负担，并且代码更难理解。

[在可能的情况下考虑使用可变参数扩展和折叠。](http://articles.emptycrate.com/2016/05/14/folds_in_cpp11_ish.html)

### 分析构建过程

工具[Templight](https://github.com/mikael-s-persson/templight)可用于分析您项目的构建时间。它需要一些工作才能构建，但一旦完成，它就可以作为 clang++的替代品。

构建使用 Templight 后，您将需要分析结果。[templight-tools](https://github.com/mikael-s-persson/templight-tools)项目提供了各种方法。（作者注：我建议使用 callgrind 转换器，并使用 kcachegrind 可视化结果）。

### 防火墙频繁更改头文件

#### 不必要包含头文件

编译器必须处理它看到的每个包含指令。即使它在看到`#ifndef`包含保护时停止，它仍然必须打开文件并开始处理它。

[include-what-you-use](https://github.com/include-what-you-use/include-what-you-use)是一个可以帮助您确定所需头文件的工具。

#### 减少预处理器的负载

这是“防火墙频繁更改头文件”和“不必要包含头文件”的一般形式。像 BOOST_PP 这样的工具可能非常有帮助，但它们也会给预处理器带来巨大的负担。

### 考虑使用预编译头文件

在大型项目中，使用预编译头文件可以显著减少编译时间。选定的头文件编译为中间形式（PCH 文件），编译器可以更快地处理它们。建议只将频繁使用但更改不频繁的头文件（例如系统和库头文件）定义为预编译头文件，以实现编译时间的减少。但是您必须记住，使用预编译头文件有几个缺点：

+   预编译头文件的使用不具有可移植性。

+   生成的 PCH 文件是机器相关的。

+   生成的 PCH 文件可能相当大。

+   它可能会破坏你的头文件依赖关系。由于预编译头文件，每个文件都有可能包含标记为预编译头文件的每个头文件。结果可能会导致如果禁用预编译头文件，则构建失败。如果你发布像库之类的东西，这可能是一个问题。因此，强烈建议启用预编译头文件构建一次，然后在第二次构建时禁用它们。

大多数常见编译器都支持预编译头文件，例如[GCC](https://gcc.gnu.org/onlinedocs/gcc/Precompiled-Headers.html)、[Clang](http://clang.llvm.org/docs/PCHInternals.html)和[Visual Studio](https://msdn.microsoft.com/en-us/library/szfdksca.aspx)。像[cotire](https://github.com/sakra/cotire/)（cmake 的插件）这样的工具可以帮助你将预编译头文件添加到你的构建系统中。

### 考虑使用工具

这些并不意味着取代良好的设计

+   [ccache](https://ccache.samba.org/)

+   [warp](https://github.com/facebook/warp)，Facebook 的预处理器

### 将 tmp 放在 Ramdisk 上

见[此](https://www.youtube.com/watch?v=t4M3yG1dWho) YouTube 视频获取更多详情。

### 使用 gold 链接器

如果在 Linux 上，考虑使用 GCC 的 gold 链接器。

## 运行时

### 分析代码！

没有真正的方法来分析代码而不知道瓶颈在哪里。

+   [`developer.amd.com/tools-and-sdks/opencl-zone/codexl/`](http://developer.amd.com/tools-and-sdks/opencl-zone/codexl/)

+   [`www.codersnotes.com/sleepy`](http://www.codersnotes.com/sleepy)

### 简化代码

代码越清洁、简单、易读，编译器实现它的机会就越大。

### 使用初始化列表

```
// This
std::vector<ModelObject> mos{mo1, mo2};

// -or-
auto mos = std::vector<ModelObject>{mo1, mo2}; 
```

```
// Don't do this
std::vector<ModelObject> mos;
mos.push_back(mo1);
mos.push_back(mo2); 
```

初始化列表效率更高；减少对象拷贝和容器大小调整。

### 减少临时对象

```
// Instead of
auto mo1 = getSomeModelObject();
auto mo2 = getAnotherModelObject();

doSomething(mo1, mo2); 
```

```
// consider:

doSomething(getSomeModelObject(), getAnotherModelObject()); 
```

这种类型的代码阻止了编译器执行移动操作…

### 启用移动操作

移动操作是 C++11 最受推崇的特性之一。它们允许编译器在某些情况下通过移动临时对象而不是复制它们来避免额外的拷贝。

我们做出的某些编码选择（比如声明自己的析构函数或赋值操作符或拷贝构造函数）阻止了编译器生成移动构造函数。

对于大多数代码，一个简单的

```
ModelObject(ModelObject &&) = default; 
```

将足够。然而，MSVC2013 似乎还不喜欢这段代码。

### 消除`shared_ptr`的拷贝

`shared_ptr`对象的拷贝成本比你想象的要高得多。这是因为引用计数必须是原子的和线程安全的。因此，这个评论只是强调了上面的注意事项：避免临时对象和过多的对象拷贝。仅仅因为我们使用了 pImpl，并不意味着我们的拷贝是免费的。

### 尽量减少拷贝和重新赋值操作

对于更简单的情况，可以使用三元运算符：

```
// Bad Idea
std::string somevalue;

if (caseA) {
  somevalue = "Value A";
} else {
  somevalue = "Value B";
} 
```

```
// Better Idea
const std::string somevalue = caseA ? "Value A" : "Value B"; 
```

更复杂的情况可以通过[立即调用的 lambda](http://blog2.emptycrate.com/content/complex-object-initialization-optimization-iife-c11)简化。

```
// Bad Idea
std::string somevalue;

if (caseA) {
  somevalue = "Value A";
} else if(caseB) {
  somevalue = "Value B";
} else {
  somevalue = "Value C";
} 
```

```
// Better Idea
const std::string somevalue = [&](){
    if (caseA) {
      return "Value A";
    } else if (caseB) {
      return "Value B";
    } else {
      return "Value C";
    }
  }(); 
```

### 避免过多异常

在正常处理期间抛出并捕获的异常会减慢应用程序的执行速度。它们还会破坏用户体验，因为调试器会监视并报告每个异常事件。尽可能避免内部异常处理是最好的。

### 摆脱“new”

我们已经知道我们不应该使用原始内存访问，所以我们使用 `unique_ptr` 和 `shared_ptr`，对吧？堆分配比栈分配昂贵得多，但有时我们不得不使用它们。更糟糕的是，创建一个 `shared_ptr` 实际上需要 2 次堆分配。

然而，`make_shared` 函数将这个问题减少到了只有一个。

```
std::shared_ptr<ModelObject_Impl>(new ModelObject_Impl());

// should become
std::make_shared<ModelObject_Impl>(); // (it's also more readable and concise) 
```

### 更倾向于使用 `unique_ptr` 而不是 `shared_ptr`

如果可能，尽量使用 `unique_ptr` 而不是 `shared_ptr`。`unique_ptr` 不需要跟踪其副本，因为它不可复制。因此，它比 `shared_ptr` 更高效。与 `shared_ptr` 和 `make_shared` 相当，你应该使用 `make_unique`（C++14 或更高版本）来创建 `unique_ptr`：

```
std::make_unique<ModelObject_Impl>(); 
```

目前的最佳实践建议从工厂函数中返回一个 `unique_ptr`，然后根据需要将 `unique_ptr` 转换为 `shared_ptr`。

```
std::unique_ptr<ModelObject_Impl> factory();

auto shared = std::shared_ptr<ModelObject_Impl>(factory()); 
```

### 摆脱 std::endl

`std::endl` 暗示着一个刷新操作。它相当于 `"\n" << std::flush`。

### 限制变量范围

变量应尽可能晚声明，并且理想情况下仅在初始化对象时才能声明。减少变量作用域会减少内存使用，更一般地提高代码效率，并帮助编译器进一步优化代码。

```
// Good Idea
for (int i = 0; i < 15; ++i)
{
  MyObject obj(i);
  // do something with obj
}

// Bad Idea
MyObject obj; // meaningless object initialization
for (int i = 0; i < 15; ++i)
{
  obj = MyObject(i); // unnecessary assignment operation
  // do something with obj
}
// obj is still taking up memory for no reason 
```

[此主题有关的讨论主题](https://github.com/lefticus/cppbestpractices/issues/52)。

### 更倾向于使用 `double` 而不是 `float`，但是先进行测试

根据情况和编译器的优化能力，其中一个可能比另一个更快。选择 `float` 将导致精度降低，并且由于转换可能会更慢。在可矢量化操作中，如果能够牺牲精度，`float` 可能会更快。

`double` 是建议的默认选择，因为它是 C++ 中浮点值的默认类型。

查看这个 [stackoverflow](http://stackoverflow.com/questions/4584637/double-or-float-which-is-faster) 讨论以获取更多信息。

### 更倾向于 `++i` 而不是 `i++`

... 当语义上是正确的。前增量比后增量 [更快](http://blog2.emptycrate.com/content/why-i-faster-i-c)，因为它不需要创建对象的副本。

```
// Bad Idea
for (int i = 0; i < 15; i++)
{
  std::cout << i << '\n';
}

// Good Idea
for (int i = 0; i < 15; ++i)
{
  std::cout << i << '\n';
} 
```

即使许多现代编译器将这两个循环优化为相同的汇编代码，但更倾向于使用 `++i` 仍然是一个好的做法。绝对没有理由不这样做，并且你永远无法确定你的代码不会通过一个不会优化此代码的编译器。你还应该意识到编译器只能为整数类型优化，而不一定是所有迭代器或其他用户定义的类型。

底线是，如果与后置递增运算符在语义上相同，那么始终更容易且建议使用前置递增运算符。

### Char 是一个字符，string 是一个字符串。

```
// Bad Idea
std::cout << someThing() << "\n";

// Good Idea
std::cout << someThing() << '\n'; 
```

这是非常微小的一点，但是一个 `"\n"` 必须被编译器解析为一个 `const char *`，当将其写入流（或附加到字符串）时，必须进行 `\0` 的范围检查。 '\n' 已知是一个单个字符，并避免了许多 CPU 指令。

如果使用效率低下的次数很多，它可能会影响您的性能，但更重要的是，思考这两种用法情况会让您更多地思考编译器和运行时如何执行您的代码。

### 永远不要使用 `std::bind`。

`std::bind` 几乎总是比你需要的开销要大得多（无论是编译时还是运行时）。 相反，只需简单地使用 lambda。

```
// Bad Idea
auto f = std::bind(&my_function, "hello", std::placeholders::_1);
f("world");

// Good Idea
auto f = [](const std::string &s) { return my_function("hello", s); };
f("world"); 
```
