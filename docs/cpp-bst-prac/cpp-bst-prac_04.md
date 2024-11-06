# 考虑安全性

# 考虑安全性

## 尽可能使用 const

`const`告诉编译器变量或方法是不可变的。这有助于编译器优化代码，并帮助开发人员知道函数是否具有副作用。此外，使用`const &`可以防止编译器不必要地复制数据。John Carmack 对`const`的[评论](http://kotaku.com/454293019)也值得一读。

```
// Bad Idea
class MyClass
{
public:
  void do_something(int i);
  void do_something(std::string str);
};

// Good Idea
class MyClass
{
public:
  void do_something(const int i);
  void do_something(const std::string &str);
}; 
```

### 仔细考虑你的返回类型

+   获取器

    +   通过`&`或`const &`返回可以在正常情况下观察返回值时节省显著的性能

    +   通过值返回对线程安全性更好，如果返回值的正常使用是进行复制，那么不会有性能损失

    +   如果你的 API 使用协变返回类型，你必须通过`&`或`*`返回

+   临时值和本地值

    +   总是通过值返回。

参考链接：[`github.com/lefticus/cppbestpractices/issues/21`](https://github.com/lefticus/cppbestpractices/issues/21) [`twitter.com/lefticus/status/635943577328095232`](https://twitter.com/lefticus/status/635943577328095232)

### 不要通过 const 引用传递和返回简单类型

```
// Very Bad Idea
class MyClass
{
public:
  explicit MyClass(const int& t_int_value)
    : m_int_value(t_int_value)
  {
  }

  const int& get_int_value() const
  {
    return m_int_value;
  }

private:
  int m_int_value;
} 
```

相反，通过值传递和返回简单类型。如果计划不更改传递的值，请将它们声明为`const`，而不是`const`引用：

```
// Good Idea
class MyClass
{
public:
  explicit MyClass(const int t_int_value)
    : m_int_value(t_int_value)
  {
  }

  int get_int_value() const
  {
    return m_int_value;
  }

private:
  int m_int_value;
} 
```

为什么？因为通过引用传递和返回会导致指针操作，而通过更快地在处理器寄存器中传递值。

## 避免原始内存访问

在 C++中，原始内存访问、分配和释放很难正确处理，而不会[出现内存错误和泄漏的风险](http://blog2.emptycrate.com/content/nobody-understands-c-part-6-are-you-still-using-pointers)。C++11 提供了避免这些问题的工具。

```
// Bad Idea
MyClass *myobj = new MyClass;

// ...
delete myobj;

// Good Idea
auto myobj = std::make_unique<MyClass>(constructor_param1, constructor_param2); // C++14
auto myobj = std::unique_ptr<MyClass>(new MyClass(constructor_param1, constructor_param2)); // C++11
auto mybuffer = std::make_unique<char[]>(length); // C++14
auto mybuffer = std::unique_ptr<char[]>(new char[length]); // C++11

// or for reference counted objects
auto myobj = std::make_shared<MyClass>(); 

// ...
// myobj is automatically freed for you whenever it is no longer used. 
```

## 使用`std::array`或`std::vector`代替 C 风格数组

这两者都保证对象的连续内存布局，并且可以（也应该）完全替代你使用裸指针的许多原因。

此外，[避免](http://stackoverflow.com/questions/3266443/can-you-use-a-shared-ptr-for-raii-of-c-style-arrays)使用`std::shared_ptr`来持有数组。

## 使用异常

异常不能被忽略。返回值，比如使用`boost::optional`，可以被忽略，如果不检查可能会导致崩溃或内存错误。另一方面，异常可以被捕获和处理。潜在地一直到应用程序的最高级别，记录并自动重新启动应用程序。

C++的原始设计者 Stroustrup，[更好地阐述了这一点](http://www.stroustrup.com/bs_faq2.html#exceptions-why)。

## 使用 C++风格的转换而不是 C 风格的转换

使用 C++风格的转换（static_cast<>, dynamic_cast<> ...）而不是 C 风格的转换。C++风格的转换允许更多的编译器检查，更加安全。

```
// Bad Idea
double x = getX();
int i = (int) x;

// Not a Bad Idea
int i = static_cast<int>(x); 
```

此外，C++转换风格更加可见，并且有搜索的可能性。

但是如果需要将`double`转换为`int`，请考虑重构程序逻辑（例如，对溢出和下溢进行额外检查）。三思而后行，少切 0.9999999999981 次。

## 不要定义可变参数函数

可变参数函数可以接受可变数量的参数。可能最为人熟知的例子是 printf()。你有可能自己定义这种函数，但这可能存在安全风险。可变参数函数的使用不是类型安全的，错误的输入参数可能导致程序以未定义的行为终止。这种未定义的行为可能被利用成为安全问题。如果你有可能使用支持 C++11 的编译器，可以使用可变模板代替。

[某些编译器技术上可以实现类型安全的 C 风格可变参数函数](https://github.com/lefticus/cppbestpractices/issues/53)

## 其他资源

[如何防止下一个 Heartbleed](http://www.dwheeler.com/essays/heartbleed.html) 是 David Wheeler 对当前代码安全状态的良好分析，以及如何确保代码安全的建议。
