# 考虑可维护性

# 考虑可维护性

## 避免使用编译器宏

编译器定义和宏在编译器运行之前由预处理器替换。这可能会使调试变得非常困难，因为调试器不知道源代码的来处。

```
// Bad Idea
#define PI 3.14159;

// Good Idea
namespace my_project {
  class Constants {
  public:
    // if the above macro would be expanded, then the following line would be:
    //   static const double 3.14159 = 3.14159;
    // which leads to a compile-time error. Sometimes such errors are hard to understand.
    static constexpr double PI = 3.14159;
  };
} 
```

## 考虑避免布尔参数

它们在阅读代码时不提供任何额外的含义。您可以创建一个具有更有意义名称的单独函数，或者传递一个使含义更清晰的枚举。

查看 [`mortoray.com/2015/06/15/get-rid-of-those-boolean-function-parameters/`](http://mortoray.com/2015/06/15/get-rid-of-those-boolean-function-parameters/) 获取更多信息。

## 避免使用原始循环

了解并掌握现有的 C++ 标准算法，并将它们应用起来。详情请参见 [C++ Seasoning](https://www.youtube.com/watch?v=qH6sSOr-yk8)。

## 永远不要在带有副作用的情况下使用`assert`

```
// Bad Idea
assert(set_value(something));

// Better Idea
[[maybe_unused]] const auto success = set_value(something);
assert(success); 
```

`assert()` 将在发布构建中被移除，这将阻止`set_value` 调用的发生。

因此，虽然第二个版本更加丑陋，但第一个版本简直是不正确的。

## 正确地利用 'override' 和 'final'

这些关键词可以让其他开发人员清楚地了解虚拟函数的使用方式，如果虚拟函数的签名发生变化，它们可以捕获潜在的错误，并且可能会向编译器[提示](http://stackoverflow.com/questions/7538820/how-does-the-compiler-benefit-from-cs-new-final-keyword)可以执行的优化。
