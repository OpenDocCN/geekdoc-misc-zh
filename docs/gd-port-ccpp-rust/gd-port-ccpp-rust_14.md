# 从 C/C++ 到 Rust 的移植。

# 在 C/C++ 中修复问题。

本节不是关于*代码应该如何正确编写，而是关于 C/C++ 语言允许什么。 连续版本的这些语言试图通过淘汰不好的一种来改良良好的实践！

所有这些事情都应该被视为不好的，语言中任何使它们成为可能的构造也都不好：

+   在基类的构造函数/析构函数中调用纯虚拟函数。

+   调用悬空指针。

+   释放内存超过一次。

+   在不遵循三大原则的情况下使用默认复制构造函数或赋值运算符。

+   溢出缓冲区，例如某些字符串操作的偏移量错误或者未测试边界条件。

+   内存泄漏是由于内存分配/所有权问题。

+   堆破坏。

C++ 编程语言是一个非常庞大的规范，每个版本都会变得越来越微妙和有限。

从程序员的角度看，问题在于理解 C++ 允许他们做什么，而不是他们应该做什么。

在每种情况下，我们将看到 Rust 如何可能阻止我们首先陷入这种情况。

## C 怎么样？

在本节中，C++ 将受到大部分批评。 有人可能倾向于认为，因此 C 不会遭受问题。

是的，在某种程度上是真的，但这相当于辩称我们不需要鞋子，因为我们没有腿。 C++ 的存在和流行是因为它被认为是从 C 进步的一步。

+   命名空间。

+   改进的类型检查。

+   类和继承。

+   异常处理。

+   更有用的运行时库，包括集合、托管指针、文件 IO 等。

模拟类并将方法绑定到它们是一项重大进步。 编写 RAII 风格代码的能力确实提高了软件保持其内存和资源使用受控制的机会。

## 编译器将捕获一些错误。

现代 C/C++ 编译器可以发现本节中提到的一些错误。 但通常它们只会抛出一个警告。 大型代码库总是会生成警告，其中许多是无害的，很容易理解为什么有些人在滚动时会对它们感到麻木。

保护 C/C++ 免受愚蠢错误的最简单方法是将严重警告提升为错误。 尽管它不会保护免受每一种错误的影响，但仍然胜过什么都不做。

+   在 Microsoft VC++ 中启用高警告级别，例如 /W4，并可能使用 /WX 将警告转换为错误。

+   在 GCC 中启用 -Wall，-pedantic-errors，并可能使用 -Werror 将警告转换为错误。 pedantic 标志拒绝不遵循 ISO C 和 C++ 标准的代码。 可以[配置](https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html#Warning-Options)许多错误。

但是这可能会在编译过程中产生大量噪音，并且其中一些错误可能超出了您控制的范围。

另外，最好运行源代码分析工具或代码检查工具。然而，这些工具往往价格昂贵，在许多情况下可能非常笨重。

# 复制构造函数/赋值运算符

# 复制构造函数/赋值运算符

在 C++中，您可以通过构造函数和赋值运算符从一个实例构造另一个实例。在某些情况下，构造函数将被用来代替赋值：

```
PersonList x; 
PersonList y = x; // Copy constructor, not assignment
PersonList z;
z = x; // Assignment operator 
```

默认情况下，C++会生成所有代码，将一个类中的字节复制到另一个类中，而无需任何努力。我们真是幸运！

因此，我们的`PersonList`类可能如下所示：

```
struct Person {
    //...
};

class PersonList {
  std::vector<Person> *personList_;
public:
  PersonList() : personList_(new std::vector<Person>) {
  }

  ~PersonList() {
    delete personList_;
  }

  // ... Methods to add / search list
}; 
```

除非我们很幸运，我们只是被弄脏了。默认的字节复制会获取`personList_`中的指针并复制它。现在，如果我们将`x`复制到`y`，或者将`x`分配给`z`，我们将有三个指向相同私有数据的类！更糟糕的是，`z`在其默认构造函数中分配了自己的`personList_`，但字节复制赋值却用`x`的那个覆盖了它，所以它的旧`personList_`值就泄漏了。

当然，我们可能可以使用`std::unique_ptr`来持有我们的指针。在这种情况下，编译器会生成一个错误。但情况可能并不总是那么简单。`personList_`可能是由外部库不透明地分配的，因此我们别无选择，只能通过构造函数和析构函数来管理其生命周期。

## 三法则

这是 C++中一个如此可怕的 bug 问题，导致了所谓的三法则^(1)。

该规则表示，如果我们在 C++类中显式声明了析构函数、复制构造函数或复制赋值运算符，那么我们可能需要实现所有三者来安全地处理赋值和构造。换句话说，修复 C++的默认和危险行为的负担落在开发人员身上。

所以让我们修复这个类：

```
struct Person {
    //...
};

class PersonList {
    std::vector<Person> *personList_;
public:
    PersonList() : personList_(new std::vector<Person>) {
    }

    PersonList(const PersonList &other) :
            personList_(new std::vector<Person>)    {
        personList_->insert(
                personList_->end(), other.personList_->begin(),
                other.personList_->end());
    }

    ~PersonList() {
        delete personList_;
    }

    PersonList & operator=(const PersonList &other) {
        // Don't forget to check if someone assigns an object to itself
        if (&other != this) {
            personList_->clear();
            personList_->insert(
                    personList_->end(), other.personList_->begin(),
                    other.personList_->end());
        }
        return *this;
    }

    // ... Methods to add / search list
}; 
```

真是一团糟！

我们已经为该类添加了一个复制构造函数和一个赋值运算符，以安全地处理复制。代码甚至还必须检查是否正在分配给自身，以防有人写了`x = x`。如果没有进行这个测试，接收实例将清除自身，准备从自身添加元素，这当然会清除其所有内容。

或者我们可以通过创建私有构造函数来禁用复制/赋值，防止外部代码调用它们：

```
class PersonList {
    std::vector<Person> *personList_;

private:
    PersonList(const PersonList &other) {}
    PersonList & operator=(const PersonList &other) { return *this; }

public:
    PersonList() : personList_(new std::vector<Person>) {
    }

    ~PersonList() {
        delete personList_;
    }
    // ... Methods to add / search list
}; 
```

另一种选择是在类内部使用不可复制类型。例如，如果指针是由 C++11 的`std::unique_ptr`（或 Boost 的`boost::scoped_ptr`）管理，则复制将失败。

Boost 还提供了一个`boost::noncopyable`类，提供了另一种选择。类可以继承自 noncopyable，它实现了一个私有的复制构造函数和赋值运算符，因此任何试图复制的代码都会生成一个编译错误。

### 五法则

在 C++11 中，由于引入了移动语义，三法则已经变成了五法则！

如果你有一个类可以受益于移动语义，那么“五大法则”基本上表示，用户定义的析构函数、复制构造函数和复制赋值运算符的存在要求你还必须实现一个移动构造函数和一个移动赋值运算符。所以除了我们上面写的代码之外，我们还必须写两个方法。

```
class PersonList {
  // See class above for other methods, rule of three....

  PersonList(PersonList &&other) {
    // TODO
  }

  PersonList &operator=(PersonList &&other) {
    if (&other != this) {
      // TODO
    }
    return  *this
  } 
```

## Rust 如何帮助

### 移动是默认值

Rust 通过使移动语义成为默认来提供帮助。也就是说，除非你需要将数据从一个实例复制到另一个实例，否则不需要。如果你将一个结构体从一个变量赋给另一个变量，所有权就会随之移动。旧变量被编译器标记为无效，访问它是一个错误。

但是如果你确实想要从一个实例复制数据到另一个实例，那么你有两个选择。

+   实现 `Clone` trait。你的结构体将有一个显式的 `clone()` 函数，你可以调用它来复制数据。

+   实现 `Copy` trait。你的结构体现在将在赋值时隐式复制而不是移动。实现 `Copy` 也意味着你仍然可以显式调用 `clone()`。

原始类型，如整数、字符、布尔等，实现了 `Copy`，所以你可以将一个赋给另一个

```
// This is all good
let x = 8;
let y = x;
y = 20;
assert_eq!(x, 8); 
```

但是 `String` 不能以这种方式被复制。字符串有一个内部的堆分配指针，所以复制是一种更昂贵的操作。因此，`String` 只实现了 `Clone` trait，它要求你显式复制它：

```
let copyright = "Copyright 2017 Acme Factory".to_string();
let copyright2 = copyright.clone(); 
```

任何结构体的默认情况是既不能被复制也不能被克隆。

```
struct Person {
  name: String,
  age: u8
} 
```

以下代码将创建一个 `Person` 对象，将其赋给 `person1`。当 `person1` 赋给 `person2` 时，数据的所有权也移动了：

```
let person1 = Person { name: "Tony".to_string(), age: 38u8 };
let person2 = person1; 
```

在所有权移动到 `person2` 后尝试使用 `person1` 将生成一个编译错误：

```
println!("{}", person1.name); // Error, use of a moved value 
```

为了说明问题，考虑一下这个 Rust 示例，它等同于我们在 C++ 中看到的 PersonList

```
struct PersonList {
    pub persons: Vec<Person>,
} 
```

我们可以看到 `PersonList` 有一个 `Vec` 向量的 `Person` 对象。在内部，`Vec` 将分配空间在堆中存储它的数据。

现在让我们来使用它。

```
let mut x = PersonList { persons: Vec::new(), };
let mut y = x;
// x is not the owner any more...
x.persons.push(Person{ name: "Fred".to_string(), age: 30u8} ); 
```

变量 `x` 在堆栈上，是一个 `PersonList`，但 persons 成员部分分配在堆上。

变量 `x` 绑定到堆栈上的 PersonList。向量在堆中创建。如果我们将 `x` 赋给 `y`，那么我们可能会有两个堆栈对象共享相同的指针在堆中，就像我们在 C++ 中所做的那样。

但是 Rust 阻止了这种情况的发生。当我们将 `x` 赋给 `y` 时，编译器将对 x 中的数据进行按位复制，但将所有权绑定到 `y`。当我们尝试访问旧变量时，Rust 生成一个编译错误。

```
error[E0382]: use of moved value: `*x.persons`
   |
10 | let mut y = x;
   |     ----- value moved here
11 | x.persons.push(Person{});
   | ^^^^^^^^^ value used here after move
   |
   = note: move occurs because `x` has type `main::PersonList`, which does not implement the `Copy` trait 
```

Rust 已经阻止了我们在 C++ 中看到的问题。不仅阻止了它，还告诉我们为什么阻止了它——值从 x 移动到 y，所以我们不能再使用 x 了。

### 实现 Copy trait

`Copy` trait 允许我们在变量之间进行直接赋值。该 trait 没有函数，并在代码中充当标记，表示应该在赋值时复制的数据。

你可以通过派生它或实现它来实现`Copy` trait。但只有结构体的所有成员也派生了该 trait，才能这样做：

```
#[derive(Copy)]
struct PersonKey {
  id: u32,
  age: u8,
}

// Alternatively...

impl Copy for PersonKey {}

impl Clone for PersonKey {
  fn clone(&self) -> PersonKey {
     *self
  }
} 
```

所以 `PersonKey` 是可复制的，因为类型 `u32` 和 `u8` 也是可复制的，编译器会接受 `#[derive(Copy)]` 指令并修改结构体的移动/复制语义。

但是当一个结构体包含一个不实现`Copy`的类型时，你会得到一个编译器错误。所以这个结构体 `Person` 会导致编译器错误，因为 `String` 没有实现`Copy`：

```
#[derive(Copy)]
struct Person {
  name: String,
  age: u8
}
// Compiler error! 
```

### 实现 Clone trait

`Clone` trait 为你的结构体添加了一个 `clone()` 函数，用于生成它的一个独立副本。如果结构体的每个成员都可以被克隆，我们可以派生它，而在 `Person` 的情况下，它可以：

```
#[derive(Clone)]
struct Person {
  name: String,
  age: u8
}
...
let x = Person { /*...*/ };
let y = x.clone(); 
```

现在，`Person` 派生了`Clone`，我们可以对 `PersonList` 做同样的事情，因为它的所有成员类型都实现了这个 trait - 一个 `Person` 可以被克隆，一个 `Vec` 可以被克隆，一个 `Box` 可以被克隆：

```
#[derive(Clone)]
struct PersonList {
    pub persons: Box<Vec<Person>>,
} 
```

现在我们可以将 `x` 克隆到 `y`，我们有了两个独立的副本。

```
//...
let mut x = PersonList { persons: Box::new(Vec::new()), };
let mut y = x.clone();
// x and y are two independent lists now, not shared
x.persons.push(Person{ name: "Fred".to_string(), age: 30} );
y.persons.push(Person{ name: "Mary".to_string(), age: 24} ); 
```

## 摘要

总之，Rust 通过将赋值视为移动来防止我们陷入麻烦，当一个不可复制的变量从一个变量赋值到另一个变量时。但如果我们想要克隆/复制，我们可以明确地表达我们的意图并这样做。

C++ 只是让我们挖了一个坑，然后把土填在我们头上。

# 条件语句中缺少大括号

# 条件语句中缺少大括号

每个程序员最终都会遇到这样的错误，并花费数小时试图弄清楚为什么它不起作用。

```
const bool result = fetch_files();
if (result) {
  process_files()
}
else
  print_error()
  return false;

// Now cleanup and return success
cleanup_files();
return true; 
```

当然，原因是 else 语句没有被大括号括起来，因此执行了错误的代码。编译器可能会在这种情况下发现死代码，但情况并不总是如此。即使它这样做了，它可能只发出警告而不是错误。

深度嵌套条件中特别容易出现问题，一个放错位置的大括号可能会附加到错误的级别上。这个问题导致了真实世界的安全问题。例如，这里就有一个臭名昭著的["goto fail"](https://www.imperialviolet.org/2014/02/22/applebug.html) bug，发生在一些苹果产品中。这个（故意的？）bug 发生在 SSL 握手期间，是可以利用的：

```
static OSStatus
SSLVerifySignedServerKeyExchange(
   SSLContext *ctx, bool isRsa, SSLBuffer signedParams,
   uint8_t *signature, UInt16 signatureLen) {
  OSStatus        err;
  //...

  if ((err = SSLHashSHA1.update(&hashCtx, &serverRandom)) != 0)
    goto fail;
  if ((err = SSLHashSHA1.update(&hashCtx, &signedParams)) != 0)
    goto fail;
    goto fail;
  if ((err = SSLHashSHA1.final(&hashCtx, &hashOut)) != 0)
    goto fail;
  //...

fail:
  SSLFreeBuffer(&signedHashes);
  SSLFreeBuffer(&hashCtx);
  return err;
} 
```

注意 "goto fail" 出现了两次，并且没有绑定到条件，而是缩进了，就好像它是。代码会直接跳转到失败标签，并返回一个指示成功的错误（因为之前的 SHA1 更新成功了）。如果条件

## Rust 如何帮助

Rust 要求 if-else 表达式和循环与块相关联。

所以这段代码无法编译：

```
let mut x: i32 = do_something();
if x == 200 {
  // ...
}
else
  println!("Error"); 
```

如果你尝试，你会得到这样的错误。

```
rustc 1.13.0-beta.1 (cbbeba430 2016-09-28)
error: expected `{`, found `println`
  |
8 |   println!("Error");
  |   ^^^^^^^
  |
help: try placing this code inside a block
  |
8 |   println!("Error");
  |   ^^^^^^^^^^^^^^^^^^
error[E0425]: unresolved name `do_something`
  |
3 | let mut x: i32 = do_something();
  |                  ^^^^^^^^^^^^ unresolved name 
```

# 条件语句中的赋值

# 条件语句中的赋值

在 `==` 条件中省略 `=` 将其转换为一个赋值，该赋值计算为 true：

```
int result = getResponseCode();
if (result = 200) { // BUG!
  // Success
}
else {
  //... Process error
} 
```

所以，在这里，结果被赋值了值 200，而不是与值 200 进行比较。编译器应该对这些情况发出警告，但是出错会更好。

开发人员也可能尝试交换左右手边来减轻问题：

```
if (200 = result) { // Compiler error
  // Success
}
else {
  // ... Process error
} 
```

现在编译器会抱怨，因为结果的值被分配给了一个常量，这没有任何意义。如果一个变量与一个常量进行比较可能会有用，但可以说这使得代码的可读性降低了，并且如果左右两边都是可分配的，则不会有帮助，因此它们的顺序并不重要。

我们在“条件语句中缺少大括号”一节中看到的`goto fail`示例还演示了将赋值和比较结合成一行的现实世界危险：

```
if ((err = SSLHashSHA1.update(&hashCtx, &serverRandom)) != 0)
  goto fail; 
```

此行之所以没有其他原因而中断，但易于看出可能存在的原因，特别是如果这种模式重复出现。程序员可能通过以这种方式组合一切来节省几行代码，但风险更大。在这种情况下，风险可能是无意中将`=`变成`==`，即将错误与函数调用进行比较，然后将其与 0 进行比较。

```
if ((err == SSLHashSHA1.update(&hashCtx, &serverRandom)) != 0)
  goto fail; 
```

## Rust 如何帮助

这段代码根本无法编译：

```
let mut result = 0;
if result = 200 { // Compile Error
  //...
} 
```

条件语句中唯一的赋值形式是专门的和显式的`if let`和`while let`形式，其他地方有解释。

# 类成员初始化

# 类成员初始化

C++不要求在每个构造函数中初始化所有变量。

+   C++类成员如果具有自己的默认构造函数，则不需要初始化。

+   C++类成员如果没有默认构造函数，则必须显式初始化。

+   引用类型的成员必须显式初始化。

+   原始类型，包括指针，不需要初始化，尽管编译器可能会警告。

+   成员不必按照声明的顺序初始化

如果忘记初始化成员或它们的顺序，一些编译器可能会发出警告，但它们仍然会编译代码。

C++11 允许类具有默认成员初始化器，如果没有构造函数设置值，则使用该初始化器将值设置为其他值：

```
class Coords {
public:
    double x = 0.0;
    double y = 0.0;
    double z = 0.0;

    // 2D initializer, x and y are set with the inputs, z is set to 0
    Coords(double x, double y) : x(x), y(y) {}
}; 
```

这显然更容易阅读，并确保如果我们有多个构造函数，那么如果默认值足够，我们就不必初始化成员。

## Rust 如何帮助

必须初始化结构体的所有成员。如果你的代码没有初始化结构体，你将得到一个编译器错误。

这将无法编译：

```
struct Alphabet {
  a: i32,
  b: u32,
  c: bool,
}

let a = Alphabet { a: -10, c: true }; 
```

如果尝试，会得到如下错误：

```
rustc 1.13.0-beta.1 (cbbeba430 2016-09-28)
error[E0063]: missing field `b` in initializer of `main::Alphabet`
  |
9 |     let a = Alphabet { a: -10, c: true };
  |             ^^^^^^^^ missing `b` 
```

强制你初始化结构体的成员确保结构体始终处于一种一致可预测的状态。

初始化的顺序并不重要，只要所有字段都被设置。

结构体通常实现一个`new()`函数，它封装了这个初始化过程，并在 C++中充当构造函数，例如：

```
struct Coord {
  pub x: f64,
  pub y: f64,
  pub z: f64,
}

impl Coord {
  pub fn new(x: f64, y:f64) {
    Coord { x: x, y: y, z: 0f64 }
  }
}
///...
let coord1 = Coord::new(100f64, 200f64); 
```

或者结构体可能会实现一个或多个`From<>`特性：

```
impl From<(f64, f64)> for Coord {
  fn from(value: (f64, f64)) -> Coord {
    Coord { x: value.0, y: value.1, z: 0.0 }
  }
}

impl From<(f64, f64, f64)> for Coord {
  fn from(value: (f64, f64, f64)) -> Coord {
    Coord { x: value.0, y: value.1, z: value.2 }
  }
}

//...
let coord = Coord::from((10.0, 20.0));
let coord = Coord::from((10.0, 20.0, 30.0)); 
```

可以有多个`From`特性实现，因此我们可以实现一种多态形式。

# 头文件和源文件

# 头文件和源文件

头文件包含了类、类型、宏等的定义，其他文件需要在`#include`中包含以解析它们对这些东西的使用。

将实现和定义拆分到不同的文件中是维护代码的额外负担，但也可能导致一些严重的错误。

+   在多个项目中使用的头文件可能具有不同的编译器设置

+   使用 `#pragma` 和对齐时可能会出现的问题

+   不同的 # 定义可能会影响字节长度

+   不同的 typedef 可能会影响字节长度

头文件的每个使用者都必须使用影响文件中每个类型、结构和类大小的确切相同设置，并解决任何影响打包/对齐的问题。如果这些设置不同，可能会导致不稳定性、损坏或仅在运行时出现的问题。

头文件还会使编译器变慢，因为消费头文件的源码不可避免地会引入其他头文件，而其他头文件又会引入其他头文件。

## 守卫块 / `#pragma once`

头文件每次被 `#include` 时都会被展开多次。为了防止每个源文件扩展超过一次，它们通常都受到守卫块的保护。

```
#ifndef FOO_H
#define FOO_H
....
#endif 
```

如果同一个头文件被多次包含，则第二次通过时会被预处理成空。

### `#pragma once`

大多数现代编译器也支持 `#pragma once` 指令。这允许编译器完全忽略已经在每个源文件中至少包含一次的 `#include`。

这比守卫块更有效，因为编译器甚至都不会再次打开或处理文件，而是直接跳过。可能会有不适合的情况，但通常会导致更快的编译速度。

### 预编译头文件

一些编译器还支持预编译头文件以加快编译速度。编译器在编译单个源文件时建立一个数据库查找，并在后续源文件编译中引用该数据库。这种解决方案可以加快编译速度，但会使构建过程变得复杂，因为一个文件具有生成预编译头文件的标志，其他源文件具有引用它的标志。

## Pimpl 模式

头文件问题的一种流行解决方法是 Pimpl 模式。这是一种将类分成公共部分和私有实现部分的方式。

公共类几乎是一个纯粹的接口定义，可以在头文件中以最小的依赖关系进行定义。它向前引用了实现类，并将其存储为成员：

```
#pragma once

// Gory details are in the .cpp file
class ComplexThingImpl;

class ComplexThing {
  ComplexThingImpl *pimpl_;
public:
  ComplexThing();
  ~ComplexThing();

  // See note 1 below

  void somethingReallyComplex();
}; 
```

外部类的构造函数将分配实现类，方法调用将通过内部调用。

私有实现类在源文件中定义，可以引入任意数量的额外头文件，`#pragma` 或其他内容，而不会影响头文件的消费者或编译时间。

```
// source file
#include "random/header.hpp"
// Lots of includes here
#include <...>
#include "more/stuff.hpp"

class  ComplexThingImpl {
  // Lots of member variables and stuff here
  // ...
public:
  void somethingReallyComplex();
}

void ComplexThingImpl::somethingReallyComplex() {
  // Lots of complex stuff here
  // ...
}

ComplexThing::ComplexThing() :
  pimpl_(new ComplexThingImpl()) {
}

ComplexThing::~ComplexThing() {
  delete pimpl_;
}

void ComplexThing:: somethingReallyComplex() {
  pimpl_->somethingReallyComplex();
} 
```

这个解决方案被称为 Pimpl（private implementation）模式，虽然它可以用来保护消费者并加快构建速度，但也增加了开发的复杂性和开销。现在不再是维护类的 2 个定义（头文件 / 源文件），而是有 4 个(!)，因为有一个公共的和一个私有的 impl 类。改变方法的签名意味着在潜在的 4 个地方进行更改，加上在公共类中调用私有对应方法的那一行。

Pimpl 的一个危险在于私有类是从堆中分配的。使用大量临时 Pimpl 对象的代码可能会导致堆碎片化。

注 1：记得三大法则吗？这也适用于这个对象。示例没有显示出来，但如果我们将 ComplexThing 复制构造或赋值给另一个实例，我们将陷入麻烦之中。所以除了解决 PImpl 的问题之外，我们还必须防止其他问题。最简单的锁定方法是从 `boost::noncopyable` 派生，如果你使用 boost，或者将复制构造函数设为 `private`，或在 C++11 中使用 delete。

## Rust 如何帮助

在 Rust 中，定义和实现是同一回事。所以我们立即有一个要维护的东西。

编写函数定义了该函数。假设我们有一个 functions.rs 文件

```
// functions.rs
pub fn create_directory_structure() {
  // Implementation
} 
```

任何人都可以将其称为 `functions::create_directory_structure()`。编译器将验证调用是否正确。

结构体的定义及其实现也只写一次。例如 `directory.rs`

```
// directory.rs
pub struct Directory {
  pub path: String,
}
impl Directory {
  pub fn mkdir(&self) {
    // implementation
  }
} 
```

实现可以在私有 Rust 模块中定义，只有公共结构体对消费者可见。

如果我们是一个库 crate（我们将其称为 `file_utils`），希望将这些对象暴露给消费者，我们将编写一个顶级 `lib.rs`，说明我们的 lib 由哪些文件组成，并且我们想要暴露哪些文件。

```
// lib.rs for file_utils
mod functions;
mod directory;
pub use functions::*;
pub use directory::Directory; 
```

现在消费者可以轻松使用我们的 crate：

```
extern crate file_utils;
use file_utils::*;
fn main() {
   create_directory_structure();
   let d = Directory { /* ... */ };
} 
```

# 前向声明

# 前向声明

C++ 防止我们引用尚未定义的类或函数。即使类或函数位于引用它的同一文件中，编译器也会抱怨。

这意味着顺序很重要。如果我们的函数或类被其他文件使用，我们必须在头文件中声明函数。如果我们的函数对一个源文件是私有的，我们必须在源文件中声明它，并可能将其设为 static。

对于类，我们可以进行前向引用。这作为一个提示，告诉编译器说类名存在，并且它会很快知道这一点。但这是一个 hack，它会限制我们如何使用前向声明的类。

例如，下面的 DataManager 可以分发 Data 对象，但 Data 对象引用了 DataManager。由于每个类相互引用，没有简单的方法让编译器满意，除了使用前向声明。

```
class Data; // Forward declaration

class DataManager {
public:
  Data *getDataById(const std::string &id);
};

class Data {
public:
  Data(DataManager &dataManager);
} 
```

但前向声明损害了代码的设计。例如，我们不能将 Data 对象保存在集合类中：

```
class Data;

class DataManager {
  std::map<std::string, Data> data_;
public:
  Data *getDataById(const std::string &id);
} 
```

编译器会抱怨，因为它不知道 Data 的构造函数或大小。因此，设计立即因为愚蠢的编译器限制而改变。例如，我们可以在 map 中存储对 Data 的指针，但然后我们就必须记得删除它。因此，前向引用增加了错误的潜在可能性。

```
class Data;

class DataManager {
  // Great, now we have to remember to new / delete Data and we increase
  // memory fragmentation
  std::map<std::string, Data*> data_;
public:
  Data *getDataById(const std::string &id);
} 
```

## Rust 如何帮助

在 Rust 中，前向声明是不必要的。结构体和函数的定义位于 .rs 文件中，并且可以通过 `use` 指令引用。

# 命名空间冲突

# 命名空间冲突

C 代码根本没有命名空间，C++ 中的命名空间是可选的。

+   C 已经学会了没有命名空间的生活。大多数 C 代码都使用函数和结构体的前缀来避免冲突，例如 `sqlite3_exec()` 是属于 SQLite3 的函数。前缀可以防止该函数与 `exec()` 发生冲突，而 `exec()` 是一个标准 POSIX 函数，它首先被引入了。因此，前缀充当了伪命名空间。但是它给我们的代码增加了噪音，并且如果支持和强制执行命名空间，则不需要它。

+   C++ 让它们易于声明，但是没有任何代码必须费心或者只是以一种非常敷衍的方式去做。

+   宏不受命名空间的影响。例如，如果某个头文件定义了 `TRUE` 和 `FALSE`，那么它们会污染所有包含了这些定义的内容。

默认情况下，所有的 C++ 代码都位于全局命名空间中：

```
void hello() {
  // My function hello is in the global namespace, i.e. ::hello()
}

int main() {
  // Main entry point
  hello();
} 
```

函数 `hello()` 属于全局命名空间。在 `main` 中对它的调用可以替换为对 `::hello()` 的调用。当然，问题在于我们往全局命名空间中写入的代码越多，或者我们引入的没有命名空间的库越多，就越有可能发生冲突。

命名空间要求将命名空间部分置于块中。

```
namespace application {
  // stuff in here belongs to application::
}
//...
application::App app("my app"); 
```

滥用命名空间也很容易，例如有时会发生这种情况，而且并不是一个好主意：

```
// Inside of foo.h...
using namespace std;
//... all code after here is tainted with std 
```

任何包含 `#include "foo.h"` 的文件都会不经意地告诉编译器自动在 std 中查找未作用域限定的类型和函数，这可能根本不是代码想要的。

嵌套命名空间也是可能的，但可能会显得混乱。

```
namespace application { namespace gui {
  // stuff in here belongs to application::gui::
} }
//... eg.
application::gui::Point2d point(100,100); 
```

如果我们忘记了在嵌套头文件中关闭大括号，那么很容易使 C++ 抛出一堆不连贯的错误。

## Rust 如何帮助

在 Rust 中，每个文件都隐式地是一个模块（等同于一个命名空间）。你不能不使用模块，因为它们会自动创建。

如果你在 crates 或 modules 的名称之间发生了冲突

# 宏

# 宏

在 C/C++ 中，宏基本上是由预处理器定义的一些规则，并且替换到编译器最终尝试编译的代码中。

现代编码实践通常使用内联函数和常量来替代宏。

但事实是它们仍然可以被（滥）用，并且代码经常这样做。例如，代码可能会插入调试语句或记录日志，在发布模式下会被编译掉。

另一个常见用法是在 Windows 上，类型`TCHAR`根据`#define UNICODE`的存在与否编译为`char`或`wchar_t`。随之而来的还有宏，如`USES_CONVERSION`、`A2CT`、`T2CW`等等。代码应该能够两种方式都能干净地编译，但现实往往并非如此。

一个经典的问题可能是这样的：

```
#define SQUARED(x) x * x
// And in code
float result = SQUARED(++x);
That would expand to
float result = ++x * ++x; 
```

因此，结果中的值将是错误的，x 中的值将增加两次。

## 编译错误

考虑我们正在编译这个结构：

```
// Header
struct Tooltip
#if TOOLTIP_VERSION > 4
  char buffer[128];
#else
  char buffer[64];
#endif
}; 
```

而在 C++中

```
Tooltip tooltip;
memset(&tooltip, 0, sizeof(tooltip)); 
```

如果我们在实现中未定义`TOOLTIP_VERSION`为与调用方相同的值，则该代码可能会覆盖整个内存，因为它认为在一个地方结构体有 128 字节，而在另一个地方有 64 字节。

## 命名空间问题

宏没有命名空间，在某些情况下，这会导致问题，其中宏定义与一个良好限定的符号发生冲突。例如，`#include <windows.h>`的代码会得到一个`#define TRUE 1`。但这排除了任何其他期望在 Windows 上编译的代码使用`TRUE`作为 const 的代码，无论它们如何合格。因此，代码必须进行一些解决方案，例如`#undef`宏来使代码工作或者使用另一个值。

```
#ifdef TRUE
#define TMP_TRUE TRUE
#undef TRUE
#endif
bool value = myapp::TRUE;
#ifdef TMP_TRUE
#define TRUE TMP_TRUE
#undef TMP_TRUE
#endif 
```

唉。但更有可能的是我们会将 myapp::TRUE 重命名为类似 myapp::MYAPP_TRUE 的东西，以避免冲突。这仍然是对宏不周到使用造成的问题的一个丑陋的解决方法。

常用单词如 TRUE、FALSE、ERROR、OK、SUCCESS、FAIL 等多多少少都因为宏而无法使用。

## Rust 如何帮助

Rust 为开发者提供了常量、内联属性以及用于条件编译的平台/架构属性。

Rust 提供了宏，但它们由一组匹配规则组成，必须生成语法上的 Rust。宏扩展是由编译器执行的，因此如果宏有错误，它就能在宏上生成错误。

# 类型不匹配

# 类型不匹配

考虑两种方法。两者都被称为 evaluate()，并且它们是重载的。主方法调用 evaluate("Hello world")。在编译代码中调用哪个版本？

```
#include <iostream>
#include <string>

using namespace std;

void evaluate(bool value) {
    cout << "Evaluating a bool " << value << endl;
}

void evaluate(const std::string &value) {
    cout << "Evaluating a string " << value << endl;
}

int main() {
    evaluate("Hello world");
    return 0;
} 
```

也许让你吃惊的是，布尔版本被调用了，而且编译器甚至都没有抱怨：

```
Evaluating a bool 1 
```

这是一个糟糕类型推断的例子。字符串字面值（char *）应该转换为 std::string（C++字符串有一个接受 char *的构造函数），但编译器选择将其视为布尔值。

在其他情况下，编译器可能会发现歧义并投诉，但 C++中类型之间的模糊界线以及重载导致了错误：这是另一个例子，编译器更加有用，通过生成一个错误来演示重载的限制

```
bool evaluate(bool value);
bool evaluate(double value); 
```

这些重载的方法应该是不同的，但对于编译器而言，它们不够不同。

总之，在 C++中关于类型的模糊和混乱规则可能导致意想不到的错误，并可能传播到运行时。

## Rust 如何帮助

在 Rust 中，函数不能以这种方式重载。

Rust 也更严格地对待类型强制转换 - 如果您有一个布尔值，您不能将其传递给接受整数的函数。

您也不能将一个大小的整数传递给接受另一个大小的整数的函数。

```
fn print_i32(value: i32) {
   println!("Your value is {}", value);
}
let value = 20i16; // 16-bit int
print_i32(value); 
```

这将导致错误：

```
error[E0308]: mismatched types
  |
7 | print_i32(value);
  |           ^^^^^ expected i32, found i16 
```

您必须使用显式的数字转换来将值转换为函数期望的类型：

```
print_i32(value as i32); 
```

# 显式 / 隐式类构造函数

# 显式 / 隐式类构造函数

混乱不止是重载可能出现的问题。C++ 对于单参数构造函数的隐式 / 显式类型转换有许多规则。

例如：

```
class MagicNumber {
public:
    MagicNumber(int value) {}
};

void magic(const MagicNumber &m) {
  //...
}

int main() {
    //...
    magic(2016);
    return 0;
} 
```

函数 `magic()` 接受一个 `const MagicNumber &`，然而我们却用 `2016` 调用它，而它仍然编译通过了。它是如何做到的？好吧，我们的 `MagicNumber` 类有一个接受 `int` 的构造函数，所以编译器隐式调用了那个构造函数，并使用了它生成的 `MagicNumber`。

如果我们不想要隐式转换（例如，也许在不知道的情况下这样做非常昂贵），那么我们就必须在构造函数中添加一个 `explicit` 关键字来否定这种行为。

```
explicit MagicNumber(int value) {} 
```

它展示了默认行为可能是错误的一个例子。默认情况下应该是 `explicit`，如果程序员想要隐式，则应该被要求明确说明。

C++11 通过允许类声明被删除的构造函数增加了混乱，这些构造函数是反构造函数，如果它们匹配，会生成一个错误而不是代码。例如，也许我们只想让隐式的 `int` 构造函数匹配，但我们想阻止某人传递一个 `double`。在这种情况下，我们可以制作一个 `double` 的构造函数，然后将其删除。

```
class MagicNumber {
public:
    MagicNumber(int value) {}
    MagicNumber(double value) = delete;
};

void magic(const MagicNumber &m) {
  //...
}

//...
magic(2016);   // OK
magic(2016.0); // error: use of deleted function 'MagicNumber::MagicNumber(double)' 
```

## Rust 如何帮助

Rust 没有构造函数，因此在构造过程中没有隐式转换。由于没有隐式转换，因此也没有理由使用 C++11 风格的函数删除操作符。

您必须编写显式的写入“构造函数”函数并显式调用它们。如果您想要重载函数，可以使用 `Into<>` 模式来实现它。

例如，我们可能会像这样编写我们的 `MagicNumber` 构造函数：

```
struct MagicNumber { /* ... */ }

impl MagicNumber {
  fn new<T>(value: T) -> MagicNumber where T: Into<MagicNumber> {
    value.into()
  }
} 
```

我们在这里说 `new()` 函数的参数是任何实现特性 `Into<MagicNumber>` 的类型 `T`。

所以我们可以为 `i32` 实现它：

```
impl Into<MagicNumber> for i32 {
   fn into(self) {
     MagicNumber { /* ... */ }
   }
} 
```

现在我们的客户端代码只需调用 `new`，并提供实现该特性的类型，我们的构造函数就会起作用：

```
 let magic = MagicNumber::new(2016);
   // But this won't work because f64 doesn't implement the trait
   let magic = MagicNumber::new(2016.0); 
```

# 弱生命周期实施

# 弱生命周期实施

这样的函数是完全合法且危险的：

```
std::string &getValue() {
  std::string value("Hello world");
  return value;
} 
```

这个函数返回一个临时变量的引用。调用它的人将获得栈上的垃圾引用。即使它看起来工作正常（例如，如果我们立即调用了引用），也只是侥幸而已。

对于这个简单的例子，我们的编译器可能会发出警告，但它不会阻止我们编译它。

## Rust 如何帮助

Rust 跟踪所有对象的生命周期，并知道它们的生命周期何时开始和结束。它跟踪对对象的引用，知道它何时被借用（传递给函数 / 作用域）。

如果检测到违反其生命周期/借用规则的任何违规行为，它会生成一个编译器错误。因此，上述代码将无法编译通过。

# 内存分配

# 内存分配

已分配的内存是从称为堆的一部分内存中请求的内存，用于某些目的，并在不再需要时返回到自由空间。

在 C 中，内存通过一个相对简单的 API 进行分配和释放：

+   `malloc` 和 `calloc` 分配内存，`free` 销毁内存。

然而，C++ 也需要调用适当的构造函数和析构函数的分配，因此除了 C 的内存分配函数外，还有分配/释放的关键字。

+   为 C++ 类实例分配/释放内存

+   用于类数组的 `new[]` 和 `delete[]`

+   上述代码通过带有作用域/共享指针类，它们接管指针的所有权，并在适当时释放它。

如果我们未能释放/删除已分配的内存，程序将泄漏内存。如果我们释放/删除已经释放的内存，程序可能会崩溃。如果我们使用 C 的 `free()` 释放一个 C++ 类，程序可能会泄漏内存，因为任何成员变量将不会被正确销毁。如果我们未能调用正确的构造函数和析构函数对，程序可能会泄漏/崩溃。

一个小型产业的工具涌现出来，专门用于尝试调试内存泄漏、崩溃等问题。像 Valgrind 等工具专门用于尝试找出谁分配了某些东西而没有释放它。

例如，这个有什么问题吗？

```
std::string *strings = new std::string[100];
//...
delete strings; 
```

糟糕，我们用 `new[]` 分配了一个字符串数组，但调用了 `delete` 而不是 `delete[]`。因此，我们没有删除一个字符串数组，而是对第一个成员调用了 delete。其中 99 个字符串的析构函数将永远不会被调用。我们应该这样写：

```
delete []strings; 
```

但是编译器并不关心，因此我们可能产生了一个潜在的难以发现的错误。

一些与内存分配相关的问题可以通过使用带有作用域或共享指针类来缓解。但是甚至有些问题可能会阻止它们正常工作。

允许内存分配跨越库边界并不是一个好主意。因此，许多库通过它们的 API 提供新的/释放函数。关于平衡调用的问题也适用于它们。

## Rust 如何帮助

在正常安全的编程过程中，Rust 没有显式的内存分配或释放。我们只需声明一个对象，它将持续存在，直到它的生命周期结束（即没有任何引用指向它了）。

这不是垃圾回收。编译器跟踪对象的生命周期，并生成代码，在不再使用该对象时自动删除它。编译器还知道，如果我们将对象的声明放在 cell、box、rc 或类似的结构中，该对象应该分配在堆上，否则应该放在堆栈上。

分配/释放只能在不安全编程中使用。除非我们与外部库或函数调用进行交互并明确将该部分标记为不安全，否则我们通常不会这样做。

# 空指针

# 空指针

需要测试指针是否为 NULL，或者盲目调用可能为 NULL 的指针已经导致了如此多的错误，以至于甚至被称为[十亿美元的错误](https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare)。

待办事项

# 虚拟析构函数

# 虚拟析构函数

C++允许类继承其他类。

在某些情况下，例如本例中，这可能导致内存泄漏：

```
class ABase {
public:
  ~ABase() {}
};

class A : public ABase {
  std::string *value_;
public:
  A() : value_(new std::string) {}
  ~A() { delete value_; }
};

void do_something() {
  ABase *instance = new A();
  //...
  delete instance;
} 
```

所以在这里我们分配了一个指向 A 的指针，将其赋值给类型为`ABase`的"instance"，对其进行操作，最后删除它。看起来没问题，但我们却泄漏了内存！当我们调用"delete instance"时，代码调用了析构函数`~ABase()`而不是析构函数`~A()`。而`value_`没有被删除，内存泄漏了。即使我们使用了作用域指针来包装`value_`，它仍然会泄漏。

代码应该这样说

```
class ABase {
public:
  virtual ~ABase() {}
}; 
```

编译器不关心我们的代码有错误。它只是为了缺少关键字而允许我们泄漏。

## Rust 如何帮助

Rust 也不使用继承，因此像上面的`ABase`那样的问题是不存在的。在 Rust 中，`ABase`将被声明为 A 实现的 trait。

```
trait ABase {
  //...
}

struct A {
  value: String,
}

impl ABase for A {
  //...
} 
```

Rust 还允许我们的结构实现另一个称为`Drop`的 trait，它相当于 C++的析构函数。

```
impl Drop for A {
  fn drop(&mut self) {
    println!("A has been dropped!");
  }
} 
```

它允许我们的代码在销毁期间执行某些操作，例如释放开放资源，记录消息或其他操作。

# 异常处理/安全

# 异常处理/安全

在 C++中，何时应该抛出异常何时应该返回代码没有硬性规定。因此，一个代码库可能有倾向于抛出大量异常，而另一个则根本不抛出。

除此之外，代码可能是异常安全的，也可能不是。也就是说，如果遇到异常，它可能会释放或不释放其资源。

已经撰写了文章来描述代码可以以何种级别的保证来进行[异常安全](http://www.boost.org/community/exception_safety.html)。

## 构造函数

您还可能被建议在构造函数中抛出异常，因为除了通过必须进行测试的标志将新对象设置为某种僵尸/死亡状态之外，否则没有简单的方法来表示对象是否出错。

```
DatabaseConn::DatabaseConn() {
  db_ = connect();
  if (db_ == NULL) {
    throw string("The database connection is null");
  }
}

// These both recover their memory
DatabaseConn db1;
DatabaseConn *db2 = new DatabaseConn(); 
```

但如果`DatabaseConn()`在抛出异常之前分配了一些内存，那么这些内存就不会被回收，因此`~DatabaseConn`将不得不清理它。

```
DatabaseConn::DatabaseConn() {
  buffer_ = new char[100];
  // ... exception throwing code
}

DatabaseConn::~DatabaseConn() {
  if (buffer_) {
    delete[] buffer_;
  }
} 
```

但如果我们等到异常抛出后才分配内存，那么`buffer_`可能就不会被设置为 NULL，因此我们必须确保将其初始化为 NULL。

```
DatabaseConn::DatabaseConn() : buffer_(NULL) {
  // ... exception throwing code
  buffer_ = new char[100];
} 
```

## 析构函数

但您将被建议不要在析构函数中抛出异常，因为在处理另一个异常时从堆栈展开期间抛出异常是致命的。

```
BadNews::~BadNews() {
    if (ptr == NULL) {
      throw string("This is a bad idea");
   }
} 
```

## Rust 如何帮助

处理错误的推荐方式是使用`Option`和`Result`类型将错误正式传递给调用者。

对于不规则的错误，你的代码可以选择调用`panic!()`，这有点像异常，因为它会导致整个线程解开。如果主线程发生 panic，那么进程将终止。

`panic!()`在某些情况下可以被捕获并恢复，但这是一种核心选项。

缺少异常可能看起来是一个坏主意，但 C++证明它们带来了许多考虑因素。

# 模板与泛型

# 模板与泛型

## 什么是模板？

C++提供了一种将类型和值替换为内联类和函数的方法，称为模板。将其视为一种复杂的替换宏 - 你在模板中指定一个类型 T，这可以在编译时替换为类型`int`或其他类型。在编译过程中，如果提供的类型存在任何错误，你将收到通知。这是一个非常强大的功能，因为它允许一个类被多种不同的类型重复使用。

模板广泛用于 C++库、Boost 和其他地方。集合、字符串、算法和各种其他代码都以一种形式或另一种形式使用模板。

然而，模板只有在实际调用内联函数时才会展开为代码。然后，如果模板调用其他模板，内联代码将一次又一次地展开，直到有一个大量的代码可以被编译。我们代码中的一个小错误可能会在一些展开的模板中产生一个巨大的错误堆栈。

例如，一个向量以它保存的类型作为模板参数。因此，我们可以创建一个`PatientRecords`的向量。

```
class PatientRecord {
  std::string name_;

  PatientRecord() {}
  PatientRecord operator= (const PatientRecord &other) { return *this; }

public:
  PatientRecord(const std::string &name) : name_(name) {
  }
};
...
std::vector<PatientRecord> records; 
```

目前为止一切顺利。所以让我们添加一条记录：

```
records.push_back(PatientRecord("John Doe")); 
```

那也可以！现在让我们尝试删除我们刚刚添加的记录：

```
records.erase(records.begin()); 
```

砰！

```
c:/mingw/i686-w64-mingw32/include/c++/bits/stl_algobase.h: In instantiation of 'static _OI std::__copy_move<true, false, std::random_access_iterator_tag>::__copy_m(_II, _II, _OI) [with _II = PatientRecord*; _OI = PatientRecord*]':
c:/mingw/i686-w64-mingw32/include/c++/bits/stl_algobase.h:396:70:   required from '_OI std::__copy_move_a(_II, _II, _OI) [with bool _IsMove = true; _II = PatientRecord*; _OI = PatientRecord*]'
c:/mingw/i686-w64-mingw32/include/c++/bits/stl_algobase.h:434:38:   required from '_OI std::__copy_move_a2(_II, _II, _OI) [with bool _IsMove = true; _II = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >; _OI = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >]'
c:/mingw/i686-w64-mingw32/include/c++/bits/stl_algobase.h:498:47:   required from '_OI std::move(_II, _II, _OI) [with _II = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >; _OI = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >]'
c:/mingw/i686-w64-mingw32/include/c++/bits/vector.tcc:145:2:   required from 'std::vector<_Tp, _Alloc>::iterator std::vector<_Tp, _Alloc>::_M_erase(std::vector<_Tp, _Alloc>::iterator) [with _Tp = PatientRecord; _Alloc = std::allocator<PatientRecord>; std::vector<_Tp, _Alloc>::iterator = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >; typename std::_Vector_base<_Tp, _Alloc>::pointer = PatientRecord*]'
c:/mingw/i686-w64-mingw32/include/c++/bits/stl_vector.h:1147:58:   required from 'std::vector<_Tp, _Alloc>::iterator std::vector<_Tp, _Alloc>::erase(std::vector<_Tp, _Alloc>::const_iterator) [with _Tp = PatientRecord; _Alloc = std::allocator<PatientRecord>; std::vector<_Tp, _Alloc>::iterator = __gnu_cxx::__normal_iterator<PatientRecord*, std::vector<PatientRecord> >; typename std::_Vector_base<_Tp, _Alloc>::pointer = PatientRecord*; std::vector<_Tp, _Alloc>::const_iterator = __gnu_cxx::__normal_iterator<const PatientRecord*, std::vector<PatientRecord> >; typename __gnu_cxx::__alloc_traits<typename std::_Vector_base<_Tp, _Alloc>::_Tp_alloc_type>::const_pointer = const PatientRecord*]'
..\vectest\main.cpp:22:34:   required from here
..\vectest\main.cpp:8:19: error: 'PatientRecord PatientRecord::operator=(const PatientRecord&)' is private
     PatientRecord operator= (const PatientRecord &other) { return *this; } 
```

如果你浏览到底部，我们可以看到`erase()`函数想要调用`PatientRecord`的赋值运算符，但由于它是私有的，所以无法调用。

但是为什么向量允许我们声明一个不符合其要求的类的向量？

我们能够声明向量，使用`std::vector::push_back()`函数，但当我们调用`std::vector::erase()`时，编译器发现了一些深层嵌套的错误，并将这些错误抛回给我们。

原因是 C++只有在调用模板时才会生成代码。因此，声明没有违规，`push_back()`也没有违规，但`erase`有。

## Rust 如何帮助

Rust 有一个类似于模板的概念，称为泛型。泛型是一个接受类型参数的结构或特性，就像模板一样。

但是类型可以通过指定必须实现的特性来强制执行。此外，任何错误都是有意义的。

假设我们想要编写一个通用函数，克隆输入值：

```
fn clone_something<T>(value: T) -> T {
  value.clone()
} 
```

我们甚至还没有调用这个函数，只是定义了它。当我们编译这个时，我们会立即在 Rust 中得到一个错误。

错误：在当前范围内找不到类型`T`的名为`clone`的方法

```
 |
4 |   value.clone();
  |         ^^^^^
  |
  = help: items from traits can only be used if the trait is implemented and in scope; the following trait defines an item `clone`, perhaps you need to implement it:
  = help: candidate #1: `std::clone::Clone` 
```

Rust 表示我们从未说明 T 是什么，因为某个随机类型没有名为 clone()的方法，所以我们得到了一个错误。因此，我们将修改函数以添加一个对 T 的特质约束。这个约束表示 T 必须实现 Clone：

```
fn clone_something<T: Clone>(value: T) -> T {
  value.clone();
} 
```

现在编译器知道 T 必须实现 Clone，它能够解析 clone()并且很高兴。接下来我们实际调用它看看会发生什么：

```
struct WhatHappensToMe;
let x = clone_something(10);
let y = clone_something(WhatHappensToMe{}); 
```

我们可以克隆整数 10，因为整数实现了 Clone 特质，但我们的空结构 WhatHappensToMe 没有实现 Clone 特质。因此当我们编译它时会得到一个错误。

```
error[E0277]: the trait bound `main::WhatHappensToMe: std::clone::Clone` is not satisfied
  |
8 | let y = clone_something(WhatHappensToMe{});
  |         ^^^^^^^^^^^^^^^
  |
  = note: required by `main::clone_something` 
```

总之，Rust 通过 TODO 改进了模板

即使它们未被使用并立即提供有意义的错误，也要编译泛型函数/结构。

允许我们将特质绑定到泛型类型，以限制我们可以传递给它们的内容。

如果我们违反特质约束的要求，会提供有意义的错误

# 多重继承

# 多重继承

C++允许代码从多个类继承，它们反过来可能会从其他类继承。这就导致了可怕的*菱形模式*。

例如，D 继承自 B 和 C，但 B 和 C 都继承自 A。那么 D 有两个 A 的实例还是一个？

这可能会导致编译器错误，只能部分地通过使用称为“虚拟继承”来说服编译器在 B 和 C 之间共享 A 来解决。

比如，如果我们知道 B 和 C 可能会被多重继承，我们可能会在它们的继承中声明一个虚拟关键字：

```
class B : public virtual A {
//...
};
class C: public virtual A {
};
class D: public B, public C {
//...
}; 
```

当 D 继承自 B 和 C 时，两者共享 A 的同一实例。但这假设 A、B 和 C 的作者意识到这个问题的出现并编码时假设 A 可以被共享。

针对菱形模式的更常见的解决方案是“不要这样做”。即使用组合或其他方法来避免这个问题。

## Rust 如何帮助

Rust 也不使用类继承，因此像菱形模式这样的问题是不存在的。

但是在 Rust 中，特质可以继承自其他特质，因此可能会出现类似菱形的问题。但为了确保它不会出现，基本特质是单独实现的，而不是与继承自它的任何特质一起实现。

因此，如果结构体 D 实现了特质 B 和 C，并且它们继承自 A，那么 A、B 和 C 必须有 impl 块。

```
trait A {
//...
}

trait B : A {
//...
}

trait C : A {
//...
}

struct D;

impl A for D {
//...
}

impl B for D {
//...
}

impl C for D {
//...
} 
```

# 链接器错误

# 链接器错误

C 和 C++要求你提供构成库或可执行文件一部分的所有.obj 文件的列表。

如果你意外地省略了一个文件，你将得到未定义或缺失的引用。维护这个文件列表是开发的额外负担，确保每次向项目添加文件时更新你的 makefile 或解决方案。

## Rust 如何帮助

Rust 包括你的库/可执行文件中直接或间接被 mod 命令引用的所有内容，从你的顶层 lib.rs 或 main.rs 开始，一直向下工作。

提供你引用一个模块，它将自动构建并链接到你的二进制文件中。

如果你使用`cargo`命令，那么上述内容也适用于你链接的外部 crate。`cargo`命令还会检查外部库之间的版本冲突。如果你发现 cargo 生成关于 crate 之间兼容性冲突的错误，你可以通过更新 Cargo.lock 文件来解决这些问题，方法如下：

```
cargo update 
```
