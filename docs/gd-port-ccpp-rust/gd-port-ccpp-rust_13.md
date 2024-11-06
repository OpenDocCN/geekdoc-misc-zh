# Rust 与 C++ 的特点对比

# Rust 与 C++ 的特点对比

Rust 和 C++ 具有大致相似的功能，尽管它们经常以不同的方式实现。

Rust 受益于学习 C/C++ 中有效和无效的东西，而且确实从各种语言中选择了功能。它还享有更清晰的 API，部分原因是像 Unicode 这样的东西决定了设计。

本节将涵盖类型、字符串、变量、字面值、集合、结构体、循环等主题。在每种情况下，它将比较 C/C++ 中的情况与 Rust 中的情况。

同样要牢记 Rust 编译成二进制代码，并且 *设计* 用于使用 C 二进制文件和被 C 二进制文件使用。因此生成的代码类似，但源代码是不同的。

# 类型

# 类型

C/C++ 编译器实现了影响标准类型宽度的 *数据模型*。一般规则是：

`1 == sizeof(char) <= sizeof(short) <= sizeof(int) <= sizeof(long) <= sizeof(long long)`

如您所见，潜在地，一直到 `long long` 都可以是单个字节，或者可能有一些其他疯狂的定义。然而，在实践中，数据模型有四种常见类型，将在下一节中介绍。

对于本节，我们将涵盖 Rust 和 C/C++ 之间 *最可能* 类似的类型。

| C/C++ | Rust | 注释 |
| --- | --- | --- |
| `char` | `i8`（或 `u8`） | C++ char 的符号性可以是有符号或无符号的 - 这里的假设是有符号的，但是目标系统有所不同。Rust 的 `char` 与 C/C++ 的 `char` 不同，因为它可以容纳任何 Unicode 字符。^(1) |
| `unsigned char` | `u8` |
| `signed char` | `i8` |
| `short int` | `i16` |
| `unsigned short int` | `u16` |
| `(signed) int` | `i32` 或 `i16` | 在 C/C++ 中，这取决于数据模型 ^(2) |
| `unsigned int` | `u32` 或 `u16` | 在 C/C++ 中，这取决于数据模型 ^(2) |
| `(signed) long int` | `i32` 或 `i64` | 在 C/C++ 中，这取决于数据模型 ^(2) |
| `unsigned long int` | `u32` 或 `u64` | 在 C/C++ 中，这取决于数据模型 ^(2) |
| `(signed) long long int` | `i64` |
| `unsigned long long int` | `u64` |
| `size_t` | `usize` | usize 可以容纳与地址空间一样大的数字 ^(3) |
| `float` | `f32` |
| `double` | `f64` |
| `long double` | ~~f128~~ | Rust 中存在对 f128 的支持，但由于在某些平台上实现它存在问题而被移除。 |
| `bool` | `bool` |
| `void` | `()` | 单位类型（见下文） |

^(1) Rust 的 `char` 类型，宽度为 4 字节，足以容纳任何 Unicode 字符。这相当于延迟出现的 `char32_t`，它出现在 C++11 中，以纠正滥用的 C++98 中的 `wchar_t` 类型，该类型在诸如 Windows 等操作系统上仅为 2 字节宽。在 Rust 中迭代字符串时，可以通过字符或 `u8` 来进行。

^(2) 请参见下一节讨论数据模型。

^(3) Rust 有一个特定的数值类型用于数组和集合的索引称为 `usize`。`usize` 被设计为能够引用与可寻址内存一样多的元素。也就是说，如果内存是 64 位可寻址的，那么 `usize` 的长度就是 64 位。还有一个称为 `isize` 的有符号类型，虽然不太常用，但也可以使用。

## 数据模型

C++ 中四种常见的数据模型是：

+   LP32 - `int` 是 16 位，`long` 和指针是 32 位。这是一个不常见的模型，是对 DOS / Windows 3.1 的一种回溯。

+   ILP32 - `int`、`long` 和指针都是 32 位。由 Win32、Linux、OS X 使用

+   LLP64 - `int` 和 `long` 是 32 位，`long long` 和指针是 64 位。由 Win64 使用

+   LP64 - `int` 是 32 位，`long` / `long long` 和指针是 64 位。由 Linux、OS X 使用

## C/C++ 类型与 Rust 的比较

C/C++ 和 Rust 将共享相应语言类型的相同机器类型以及相同的编译器 / 后端技术，即：

1.  有符号类型是二进制补码

1.  IEE 754-2008 二进制 32 位和 64 位浮点数类型的浮点数和双精度类型。

## stdint.h / cstdint

C 提供了一个 `<stdint.h>` 头文件，提供了具有长度和符号的清晰 typedefs，例如 `uint32_t`。C++ 中的等效物是 `<cstdlib>`。

如果您使用此头文件中定义的类型，则类型在 C/C++ 和 Rust 之间变得直接类比和清晰。

| C/C++ | Rust |
| --- | --- |
| `int8_t` | `i8` |
| `uint8_t` | `u8` |
| `int16_t` | `i16` |
| `uint16_t` | `u16` |
| `uint32_t` | `u32` |
| `int32_t` | `i32` |
| `int64_t` | `i64` |
| `uint64_t` | `u64` |

## 整数类型

### C++

C/C++ 中有用于数值、浮点数和布尔值的原始类型。字符串将在单独的部分中处理。

整数类型（`char`、`short`、`int`、`long`）有 `signed` 和 `unsigned` 版本。

`char` 总是 8 位，但出于历史原因，标准仅保证其他类型至少是某个位数。因此，`int` 通常是 32 位，但标准只规定它应该至少与 `short` 一样大，因此潜在地它可能是 16 位！

较新版本的 C 和 C++ 提供了一个 [`<cstdint>`](http://www.cplusplus.com/reference/cstdint/)（或 `<stdint.h>` 用于 C）具有清晰关于精度的 typedefs。

即使 `<stdint.h>` 可以消除模糊性，代码经常为简洁性而牺牲正确性。在循环中经常看到一个 `int` 用作临时增量值：

```
string s = read_file();
for (int i = 0; i < s.size(); ++i) {
  //...
} 
```

尽管在大多数支持 ILP32 或更大的现代编译器中，`int` 不太可能失败，但这仍然是技术上的错误。在 LP32 数据模型中，将 32767 加一会变成 -32768，因此如果 `s.size()` 的值大于那个值，这个循环永远不会终止。

但再次看这个片段。如果由 `read_file()` 读取的文件不受我们控制，会怎么样。如果有人故意或者不小心地给我们提供一个超出我们循环迭代的文件呢？这样做，我们的代码就彻底坏掉了。

这个循环应该使用与 `string::size()` 返回的相同类型，这是一个称为 `size_type` 的不透明无符号整数类型。这通常是 `std::size_t` 的 typedef，但不一定是这样。因此，我们有一个类型不匹配。一个 `string` 有一个迭代器，可以使用它，但也许你因为某种原因需要索引，但可能会很混乱：

```
string s = read_file();
for (string::iterator i = s.begin(); i != s.end(); ++i) {
  string::difference_type idx = std::distance(s.begin(), i);
  //...
} 
```

现在我们从一个不透明类型 `size_type` 切换到另一个称为 `difference_type` 的类型。呃。

C/C++ 类型也可能是不必要的冗长，例如 `unsigned long long int`。同样，这种膨胀的写法会鼓励代码做出错误的假设，使用更少字的类型，或者用 typedefs 来膨胀代码。

## Rust

Rust 从整数类型中受益，这些整数类型在名称中明确地表示了它们的有符号性和宽度 - `i16`、`u8` 等等。

它们也非常简洁，易于声明和使用。例如，`u32` 是一个无符号的 32 位整数。`i64` 是一个有符号的 64 位整数。

类型可以被推断或显式前缀到值上：

```
let v1 = 1000;
let v2 : u32 = 25;
let v3 = 126i8; 
```

Rust 还有两种类型分别称为 `usize` 和 `isize`。它们与 `size_t` 等效，因为它们足够大以容纳地址内存中的元素数量。因此，在 32 位操作系统中，它们的大小为 32 位，在 64 位操作系统中，它们的大小为 64 位。

Rust 不会隐式地将一个大小的整数转换为另一个大小，除非明确使用 `as` 关键字。

```
let v1 = 1000u32;
let v2: u16 = v1 as u16; 
```

## 实际类型

### C++

C/C++ 中有 `float`、`double` 和 `long double` 等浮点类型，它们与整数类型一样存在模糊性。

+   `float`

+   `double` - "至少与 `float` 一样精确"

+   `long double` - "至少与 `double` 一样精确"

在大多数编译器和架构中，一个 float 是一个 32 位单精度值，一个 double 是一个 64 位双精度值。最常见的机器表示形式是 [IEEE 754-2008 格式](https://en.wikipedia.org/wiki/IEEE_floating_point)。

#### Long double

[`long double`](https://en.wikipedia.org/wiki/Long_double) 对于编译器来说已经非常棘手了。尽管预期它是一个四倍精度的值，但通常并非如此。一些编译器，如 gcc，可能在具有浮点单位的 x86 处理器上提供 80 位扩展精度，但这是实现定义的行为。

微软 Visual C++ 编译器将其视为与 `double` 相同精度的类型。其他架构可能将其视为四倍精度。`long double` 的根本问题在于，大多数桌面处理器在硬件上没有执行 128 位浮点操作的能力，因此编译器必须在软件中实现它或者不理会。

#### 数学函数

C 头文件 `<math.h>` 提供了用于处理不同精度类型的数学函数。

```
#include <math.h>

const double PI = 3.1415927;
double result = cos(45.0 * PI / 180.0);
//..
double result2 = abs(-124.77);
//..
float result3 = sqrtf(9.0f);
//
long double result4 = powl(9,10); 
```

注意不同的精度需要不同的调用，例如 sinf、sin 或 sinl。C99 在 `<tgmath.h>` 中提供了一组"类型通用"的宏，允许无论类型如何都可以使用 sin。

C++11 提供了一个`<cmath>`，使用专门的内联函数来实现相同的目的：

```
#include <cmath>
float result = std::sqrt(9.0f); 
```

### Rust

Rust 实现了两种浮点数类型 - `f32`和`f64`。这些将类似于 C/C++中的 32 位`float`和 64 位`double`。

```
let v1 = 10.0;
let v2 = 99.99f32;
let v3 = -10e4f64; 
```

与 C/C++不同，数学函数直接绑定到类型本身，只要你正确限定类型即可。

```
let result = 10.0f32.sqrt();
//
let degrees = 45.0f64;
let result2 = angle.to_radians().cos(); 
```

Rust 没有 128 位双精度浮点数。在某段时间内确实存在`f128`，但由于可移植性、复杂性和维护问题而被移除。注意根据编译器和目标平台处理（或不处理）`long double`的方式。

在某个时候，Rust 可能会获得一个 f128 或 f80，但目前还没有这样的类型。

## 布尔值

在 C/C++中，`bool`（布尔）类型可以有值`true`或`false`，但它可以提升为整数类型（0 == `false`，1 == `true`），而且布尔类型甚至有一个++运算符，用于将 false 转换为 true，尽管它没有--运算符！？

但是，将 true 反转为!false，反之亦然。

```
!false == true
!true == false 
```

Rust 也有一个`bool`类型，它的值可以是`true`或`false`。与 C/C++不同，它是一个真正的类型，没有提升为整数类型

## void / Unit 类型

C/C++使用`void`来指定无类型或不确定指针指向的内容。

```
// A function that doesn't return anything
void delete_directory(const std::string &path);

// Indeterminate pointer use
struct file_stat {
  uint32_t creation_date;
  uint32_t last_modified;
  char file_name[MAX_PATH + 1];
};

// malloc returns a void * which must be cast to the type need
file_stat *s = (file_stat *) malloc(sizeof(file_stat));
// But casting is not required when going back to void *
free(s); 
```

在 Rust 中，与`void`最接近的东西是 Unit 类型。它被称为 Unit 类型，因为它的类型是`()`，并且有一个值是`()`。

从技术上讲，`void`绝对什么也不是，`()`是一种`()`类型的单个值，因此它们不是类似的，但它们具有类似的用途。

当一个块评估为无时，它返回`()`。我们也可以在我们不关心一个参数的地方使用它。例如，假设我们有一个函数`do_action()`，它因各种原因成功或失败。我们不需要 Ok 响应的任何有效负载，所以将`()`指定为成功的有效负载：

```
fn do_action() -> Result<(), String> {
 //...
 Result::Ok(())
}

let result = do_action();
if result.is_ok() {
 println!("Success!");
} 
```

### 空枚举

Rust 确实有与`void`更接近（但不完全相同）的东西 - 空枚举。

```
enum Void {} 
```

本质上，此枚举根本没有任何值，因此任何分配或匹配此无值的操作都是无法到达的，编译器可以发出警告或错误。如果代码使用了`()`，编译器可能无法确定这一点。

## 元组

元组是一个传递给函数或由函数返回的相同类型或不同类型值的集合，就好像它是一个单一的值一样。

C/C++没有元组原始类型的概念，但是 C++11 可以使用模板构造元组：

```
std::tuple<std::string, int> v1 = std::make_tuple("Sally", 25);
//
std::cout << "Name = " << std::get<0>(v1)
          << ", age = " << std::get<1>(v1) << std::endl; 
```

Rust 支持元组作为其语言的一部分：

```
let v1 = ("Sally", 25);
println!("Name = {}, age = {}", v1.0, v1.1); 
```

正如你所看到的，这更简洁更实用。请注意，元组的索引方式与数组不同，值通过`.0`，`.1`等索引。

元组也可以被函数返回，赋值运算符可以忽略我们不感兴趣的元组成员。

```
let (x, y, _) = calculate_coords();
println!("x = {}, y = {}", x, y);
//...
pub fn calculate_coords() -> (i16, i16, i16) {
  (11, 200, -33)
} 
```

在此示例中，calculate_coords()函数返回一个包含三个`i16`值的元组。我们将前两个值分别赋给`x`和`y`，并通过传递下划线来忽略第三个值。下划线告诉编译器我们知道第 3 个值，但我们只是不关心它。

元组在代码块中可能特别有用。例如，假设我们想从一个使用引用计数服务上的保护锁的代码段中获取一些值。我们可以在块中锁定服务并将所有值作为元组返回给块外的接收者：

```
let protected_service: Arc<Mutex<ProtectedService>> = Arc::new(Mutex::new(ProtectedService::new()));
//...
let (host, port, url) = {
  // Lock and acquire access to ProtectedService
  let protected_service = protected_service.lock().unwrap();
  let host = protected_service.host();
  let port = protected_service.port();
  let url = protected_service.url();
  (host, port, url)
} 
```

这段代码确实很简洁 - 锁允许我们获取值，锁超出范围后一次返回所有值。

## 数组

数组是在堆栈或堆上分配的固定大小元素列表。

例如，在 C++ 中创建一个包含 100 个 `double` 值的数组：

```
// Stack
double values[100];
// Heap
double *values = new double[100];
delete []values;
// C99 style brace enclosed lists
double values[100] = {0}; // Set all to 0
double values[100] = {1, 2, 3}; // 1,2,3,0,0,0,0...
// C99 with designator
double values[100] = {1, 2, 3, [99] 99}; // 1,2,3,0,0,0,...,0,99 
```

而在 Rust 中：

```
// Stack
let mut values = [0f64; 100]; // 100 elements 
let mut values = [1f64, 2f64, 3f64]; // 3 elements 1,2,3
// Heap
let mut values = Box::new([0f64; 100]); 
```

请注意 Rust 提供了一种用相同值初始化数组的简写方式，或者使用封闭列表语法设置数组的每个值。在 C 和 C++ 中，初始化是可选的，但使用封闭列表语法可以更具表现力地设置或不设置数组的某些部分。

Rust 实际上*强制*您将数组初始化为某些值。尝试声明一个数组而不为其分配值将导致编译器错误。

## 切片

切片是数组或字符串的一部分的运行时视图。切片不是数组/字符串的副本，而是对其中一部分的引用。引用保存指向起始元素的指针以及切片中的元素数。

```
let array = ["Mary", "Sue", "Bob", "Michael"];
println!("{:?}", array);
let slice = &array[2..];
println!("{:?}", slice); 
```

此切片表示从索引 2 开始的数组部分。

```
["Mary", "Sue", "Bob", "Michael"]
["Bob", "Michael"] 
```

### 数组的大小

C 和 C++ 基本上没有简单的方法来知道数组的长度，除非您使用 `std::array` 封装数组或者记得从声明数组的代码中获取它。

```
// C++11
std::array<Element, 100> elements;
std::cout << "Size of array = " << elements.size() << std::endl; 
```

`std::array` 包装器的用途有限，因为您无法将未知大小的数组传递给函数。因此，即使使用此模板，您也可以将数组作为一个参数传递给函数，将其大小作为另一个参数。

或者您可能会看到类似这样的代码：

```
const size_t num_elements = 1024;
char buffer[num_elements];
//...
// fill_buffer needs to be told how many elements there are
fill_buffer(buffer, num_elements); 
```

或者像这样

```
Element elements[100];
//...
int num_elements = sizeof(elements) / sizeof(Element); 
```

在 Rust 中，数组有一个名为 `len()` 的函数与之绑定。这始终提供数组的长度。此外，如果我们取数组的切片，那也有一个 `len()`。

```
let buffer: [u8; 1024]
println!("Buffer length = {}", buffer.len());

fill_buffer(&buffer[0..10]);
//...
fn fill_buffer(elements: &[Element]) {
  println!("Number of elements = {}", elements.len());
} 
```

# 字符串

# 字符串

由于语言和字符以不同的方式映射到字节上，C++ 中的字符串有点混乱。对此的解释需要一些背景知识...

## 字符究竟是什么？

在 C 和 C++ 中，历史上 char 类型是 8 位。严格来说，char 是有符号类型（通常为 -128 到 127），但这些值实质上表示值 0-255。

美国 ASCII 标准使用前 7 位（0-127）为英文字母、数字、标点符号和某些控制字符分配值。

这对于使用不同字符集的其他国家并没有帮助。即使 ASCII 也与另一个称为 EBDIC 的标准竞争，后者在大型计算机上找到。

那么 128-255 的上限值呢？一些操作系统提出了一个称为“代码页”的概念。根据实施的“代码页”，用户在 128-255 范围内看到的字符符号将会改变。

但即使这还不够。一些语言，如中文、日文、韩文、泰文、阿拉伯文等，有成千上万的符号，必须用多个字节进行编码。因此，第一个字节可能是一个修饰符，与后续字节组合以呈现为一个符号。例如，微软的代码页 932 使用了一个称为 Shift JIS（日文）的编码，其中一些符号是两个字节。

显然，这很快变得一团糟。每个代码页根据某些外部设置以不同方式解释相同的字节数组。因此，您不能将用中文编写的文件发送给具有不同代码页的人，并期望它正确呈现。

### Unicode 来拯救

Unicode 标准为每个存在的可打印符号分配了一个唯一的 32 位值，称为代码点。大多数符号位于称为基本多语言平面（BMP）的前 16 位中。

中国规定所有软件必须支持所有 32 位。我们将看到这对 C 和 C++造成了重大困扰。

## C / C++

### 没有字符串原始类型

C 和 C++ 没有字符串原始类型，而是有一个长度为一个字节的`char`类型。一个“字符串”是指一个指向以零字节`'\0'`结尾的字符数组的指针。

```
// The array that my_string points at ends with a hidden \0
char *my_string = "This is as close to a string primitive as you can get"; 
```

在 C 中，诸如`strlen()`、`strcpy()`、`strdup()`等函数允许对字符串进行操作，但它们通过使用零字节来计算事物的长度。因此，`strlen()`是在找到`\0`之前遇到的字节数。由于这些函数运行直到找到终止字符，很容易意外地使它们超出缓冲区。

在 C++ 中，`std::string`类包装了一个 char 指针，并提供了安全的方法来以安全的方式修改字符串。这比 C 有了很大的改进，但它仍然不是一个原始类型 - 它是一个在头文件中定义的类，与可执行文件一样被编译和链接。

此外，`std::string`通常会使用堆来存储字符串的数据，这可能会对内存使用和碎片化产生影响。将一个字符串分配给另一个字符串通常会有隐藏的成本，因为必须分配内存来接收字符串的副本，即使在分配过程中字符串本身没有被修改。

### Unicode 支持

C/C++通过创建一个称为`wchar_t`的宽字符来添加 Unicode 支持。C++有一个等效的`std::wstring`。

我们现在已经排序好了对吧？

糟糕，因为`wchar_t`类型可以是 2 或 4 字节宽，这是编译器/平台特定的决定。

在 Microsoft Visual C++中，宽字符是一个`unsigned short`（对应于 Win32 的 Unicode API），在 gcc 中，根据编译标志，它可以是 32 位或 16 位。

16 位值将包含来自基本多语言平面的符号，但不包括完整的 32 位范围。这意味着应该假定 16 位宽的字符串是 UTF-16 编码的，因为否则无法正确支持 Unicode。

C++11 通过引入显式的`char16_t`和`char32_t`类型以及相应版本的字符串`std::u16string`和`std::u32string`来纠正这一点。

### 字符类型

所以现在 C++有 4 种字符类型。很棒，对吧？

| 字符类型 | 编码 |
| --- | --- |
| `char` | C，ASCII，EBDIC，UTF-8，ad hoc，??? |
| `wchar_t` | UTF-16 或 UTF-32 |
| `char16_t` | UTF-16 |
| `char32_t` | UTF-32 |

## Rust

Rust 非常幸运。Unicode 在它之前出现，所以它做了一个非常简单的设计选择。

+   `char`类型是一个 32 位的 Unicode 字符，始终足以容纳一个单一字符。

+   `str`类型是一个 UTF-8 编码的字符串，保存在内存中。代码倾向于使用`&str`，它是一个字符串切片，基本上是对 str 的引用，或者是其中的一部分。一个 str 不需要以零字节结尾，如果需要的话，可以包含零字节。

+   一个`std::String`是一个堆分配的字符串类型，用于操作字符串，构建字符串，从文件中读取字符串，克隆字符串等。

注意，内部使用 UTF-8 进行编码，但一个字符是 32 位的。字符串的长度被认为是其字节长度。有特殊的迭代器用于遍历字符串并将 UTF-8 解码为 32 位字符。

最后有一个特定于平台的类型`OSString`，处理操作系统如何看待字符串与 Rust 的区别。

## 类型比较

| C++ | Rust |
| --- | --- |
|  | `char *`或`wchar_t *` |
| C++11 - `char16_t *`, `char32_t *` | `str`, `&str` |
|  | `std::string`，`std::wstring` |
| `std::u16string` `std::u32string` | `std::String` |

## char * vs str

C/C++没有字符串原语。一个字符串是指向内存中的一些字节的指针，这些字节是以空字符结尾的。对于更宽的字符，同样适用，只是它们需要 2 或 4 个字节。

```
// The traditional way
char *my_str = "Hello"; // Terminates with \0
// or
char my_str[] = "Hello"; // Terminates with \0
// or wide string with L prefix
wchar_t hello_chinese = L"\u4f60\u597d";
// C11 and C++11 add UTF string literal prefixes
auto hello_8  = u8"\u4f60\u597d"; // UTF-8 encoded
auto hello_16 =  u"\u4f60\u597d"; // UTF-16
auto hello_32 =  U"\u4f60\u597d"; // UTF-32 
```

Rust 会使用`str`来实现这个目的。`str`是一个在内存中的*不可变*字节数组。当它指向一个`String`对象时，该`str`可能在堆上，或者如果字符串是静态的，则可能在全局内存中。一个 str *slice* 是 `&str`，是对 str 的引用，也包含一个长度值。

```
let my_str = "Hello";
let hello_chinese = "你好"; 
```

对于这些赋值，类型推断会创建一个指向静态分配的字符串数据的字符串切片。数据本身不会移动，而`&str`是只读的。

我们还可以观察到，Rust 消除了 C 和 C++必须忍受的字符宽度和字面前缀的混乱，因为 Unicode 字符是隐式支持的。

`str`有一些函数用于按字节/字符迭代字符串，拆分字符串，查找模式等。

```
let my_str = "Hello"; // v is a &’static str
println!("My string is {} and it is {} bytes long", v, v.len()); 
```

注意`len()`是以字节为单位的长度，因为字符串是 UTF-8 编码的。一个单一字符可能被编码为 1、2、3 或 4 个字节。这可能不是一个人类实际看到的字符数。

```
let my_str = "你好";
println!("Number of bytes = {}", my_str.len());
println!("Number of chars = {}", my_str.chars().count()); 
```

```
Number of bytes = 6
Number of chars = 2 
```

你可以通过拆分`&str`来生成左右`&str`切片，就像这样：

```
let (part1, part2) = "Hello".split_at(3);
println!("Part 1 = {}", part1);
println!("Part 2 = {}", part2); 
```

```
Part 1 = Hel
Part 2 = lo 
```

## std::basic_string（C++） vs std::String（Rust）

标准的 C++ 库还有模板类 `std::basic_string`，它充当各种字符类型的包装器，并可用于操作任意宽度的字符串。这个模板被专门化为

`std::string`, `std:wstring`, `std::u16string` 和 `std::u32string`。

```
std::string my_str = "Hello";
my_str += " world";

// C++11 also allows some type inference with autos
auto s1 =   "Hello"s; // std::string
auto s2 = u8"Hello"s; // std::string, forces UTF-8 encoding
auto s3 = L"Hello"s;  // std::wstring
auto s4 = u"Hello"s;  // std::u16string
auto s5 = U"Hello"s;  // std::u32string 
```

在 Rust 中，`std::String` 类型具有相同的作用：

```
let v = String::from("Hello");
v.push_str(" world"); 
```

使用它相当简单。

```
let mut v = String::from("This is a String");
v.push_str(" that we can modify"); 
```

`String` 有用于执行诸如追加等操作的函数，例如：

```
let b = String::from(" Bananas");
let mut result = String::new();
result.push_str("Apples ");
result.push('&'); // Push a char
result.push_str(b.as_str());
println!("result = {}", result); 
```

字符串始终是有效的 UTF-8。

字符串内部有指向数据的指针，它的长度和容量（最大大小）。如果你打算扩展一个字符串，那么你应该确保 `String` 有足够的容量来容纳其最长的值，否则你可能会导致它过度重新分配。

字符串永远不会缩小其容量，除非你显式调用 `shrink_to_fit()`。这意味着如果你在循环中使用临时字符串，最好将其放在循环外，并预留空间以使其高效。

```
let mut v = String::with_capacity(100);
// or
let mut v = String::new();
v.reserve_exact(100); 
```

字符串还具有所有 `str` 的方法，这得益于实现了 `Deref` 特性。

### 格式化字符串

字符串可以用 `printf` 或 `sprintf` 在 C 中格式化，或者在 C++ 中使用流运算符组合，例如，到 `std::stringstream`。

Rust 使用 `format!` 和 `println!` 宏，这更类似于 `sprintf` 模型。

| C++ | Rust 格式化特性 | 用途 |
| --- | --- | --- |
| `%s`, `%u`, `%d`, `%i`, `%f`, `%c` | `{}` | C/C++ 需要指定参数的类型。在 Rust 中，类型是推断的，而 `{}` 会调用类型的 Display 特性，无论它是什么。因此，String 输出其文本，数值类型返回其值，布尔类型返回 true 或 false，依此类推。 |
| `%lld`, `%llu` | `{}` | C/C++ 有处理不同大小整数和浮点数的扩展，例如，由于参数传递给函数的方式，long long 会用 ll 表示。在 Rust 中，这是不需要的。 |
|  | `{:?}`, `{:#?}` | 在 Rust 中，`{:?}` 返回类型实现的 Debug 特性。`{:#?}` 变体可用于漂亮地打印实现 Debug 特性的类型的输出。 |
| `%-10s` | `{:<10}` | 格式化为左对齐字符串，填充到至少 10 个空格。 |
| `%04` | `{:04}` | 将数字填充到 4 位宽度的零 |
| `%.3` | `{:.3}` | 将数字的精度填充到 3 位小数。也可以进行零填充，例如：{:.03} |
| `%e`, `%E` | `{:e}`, `{:E}` | 指数，小写或大写 |
| `%x`, `%X` | `{:x}`, `{:X}` | 十六进制，小写或大写。请注意，`{:#x}`、`{:#X}` 会在输出前面加上 0x。 |
| `%o` | `{:o}` | 八进制。请注意，`{:#o}` 会在输出前面加上 0o。 |
|  | `{:b}` | 二进制。请注意，`{:#b}` 会在输出前面加上 0b。 |
| `%p` | `{:p}` | 显示结构体的内存位置，即指针 |

Rust 比这还有[更多的格式化特性](https://doc.rust-lang.org/std/fmt/#formatting-traits)。

例如，它允许像这个例子这样的命名参数：

```
let message = format!("The temperature {temp}C is within {percent} of maximum", temp = 104, percent = 99); 
```

命名参数在本地化中特别有用，因为一个语言中值的顺序可能与另一种语言中的不同。

## 显示和调试特征

Rust 允许根据它们实现的格式化特征将类型格式化为字符串。

两个主要的实现特征是：

+   `Display` - 用于类型的标准文本表示。

+   `Debug` - 用于类型的调试文本表示。它可能提供额外信息或单独格式化以供调试。通常通过 `#[derive(Debug)]` 实现此特征，这通常足够用于调试目的。

如果我们查看特征，我们会发现它们是相同的

```
// std::fmt::Display
pub trait Display {
    fn fmt(&self, &mut Formatter) -> Result<(), Error>;
}
// std::fmt::Debug
pub trait Debug {
    fn fmt(&self, &mut Formatter) -> Result<(), Error>;
} 
```

所有内置类型都实现了 `Display` 和 `Debug`。我们也可以在自己的结构体上显式实现 Display：

```
use std::fmt::{self, Formatter, Display};

struct Person {
  first_name: String,
  last_name: String,
}

impl Display for Person {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "{} {}", self.first_name, self.last_name)
  }
}
//...
let person = Person { first_name: "Susan".to_string(), last_name: "Smith".to_string() };
println!("Person - {}", person); 
```

```
Person - Susan Smith 
```

通常通过 `#[derive(Debug)]` 实现 `Debug`，但也可以手动实现。派生的 `Debug` 将打印出结构体名称，然后是花括号中的成员：

```
#[derive(Debug)]
struct Person {
  //...
}
//...
println!("Person - {:?}", person); 
```

```
Person - Person { first_name: "Susan", last_name: "Smith" } 
```

许多类型处理格式化特征，这些特征是字符串中 `{}` 括号之间保存的值。这些与 C 函数中用于 printf、sprintf 等的模式非常相似。

## OsString / OsStr

Rust 认识到有时需要从系统 API 传递或接收字符串。

在这种情况下，您可以使用 `OsString`，它允许在 Rust 和系统相关的字符串表示之间进行交换。在 Windows 上，它将返回 UTF-16 字符串，在 Linux / Unix 系统上，它将返回 UTF-8。

`OsStr` 是对 `OsString` 的切片，类似于 `str` 和 `String`。

# 变量

# 变量

## C++

### 类型推断

C++11 具有类型推断，之前的版本不具备。类型推断允许程序员将值赋给 `auto` 类型的变量，让编译器根据赋值推断类型。

布尔和数值类型相对容易理解，只要代码尽可能明确。

```
auto x = true; // bool
auto y = 42;   // int
auto z = 100.; // double 
```

C++ 处理数组和字符串时会变得混乱。请记住，在 C 或 C++ 中，字符串不是原始类型，因此 `auto` 需要明确定义它们，否则类型将错误。

```
auto s = std::string("Now is the window of our discontent"); // char string
auto s = U"Battle of Waterloo"; // char32_t pointer to UTF-32 string literal 
```

字符串在其他地方有涵盖，但基本上有许多种类的字符串，C++/C 已经发展出了一大堆字符串前缀来处理它们。

数组是一个更有趣的问题。`auto` 关键字没有简单的方法推断数组类型，因此将模板化数组分配给 `auto` 并强制转换是一种解决方法。

```
template <typename T, int N> using raw_array = T[N];
auto a = raw_array<int, 5>{}; 
```

## Rust

在 Rust 中，变量使用 `let` 命令声明。`let` 可能指定变量的类型，也可以使用类型推断从赋值的值中推断出类型。

```
let x = true; // x: bool
let y = 42; // y: i32
let z = 100.0; // z: f64
let v = vec![10, 20, 30]; // v: Vec<i32>
let s = "Now is the winter of our discontent".to_string(); // s: String
let s2 = "Battle of Waterloo"; // s2: &str
let a1: [i32; 5] = [1, 2, 3, 4, 5]; 
```

Rust 在数组赋值中使用类型推断没有问题：

```
let a2 = ["Mary", "Fred", "Sue"]; 
```

请注意，所有数组元素必须是相同类型，推断会为这样的数组生成编译器错误：

```
// Compile error
let a3 = ["Mary", 32, true]; 
```

## 作用域规则

C、C++ 和 Rust 中的作用域规则相当相似 - 声明项目的作用域决定了其生命周期。

### 变量的阴影

Rust 的一个非常有用的特性是你可以在相同的作用域或嵌套作用域中多次声明同名变量，编译器不会介意。事实上，你会经常使用这个特性。

这被称为*遮蔽*，并且像这样工作：

```
let result = do_something();
println!("Got result {:?}", result);
if let Some(result) = result {
  println!("We got a result from do_something");
}
else {
  println!("We didn't get a result from do_something");
}

let result = do_something_else();
//... 
```

此示例三次使用变量名`result`。首先是为了存储调用`do_something()`的结果，然后是从`Option<Foo>`中提取某个值`Foo`，第三次是为了调用其他东西。我们本可以将`result`赋值给`result2`，然后稍后将值`do_something_else()`赋给`result3`，但由于遮蔽的原因我们不需要这样做。

## 指针

### 在 C++ 中

指针是指向内存中某个地址的变量。指针的*类型*指示编译器在地址处应该期望什么，但没有强制要求确保地址实际上保存了该类型。指针可能被赋值为`NULL`（或在 C++11 中为`nullptr`），或者甚至可能是垃圾，如果没有给它赋值的话。

```
char *name = "David Jones";

int position = -1;
find_last_index("find the letter l", 'l', &position); 
```

通常在无法使用引用的情况下使用指针，例如返回分配的内存的函数或父/子集合关系，在这种情况下，循环依赖会阻止使用引用。

C++11 弃用了`NULL`，改用了新关键字`nullptr`来解决函数重载的问题。

```
void read(Data *data);
void read(int value);
// Which function are we calling here?
read(NULL); 
```

由于`NULL`本质上是`#define NULL 0`，而 0 是一个整数，我们意外地调用了错误的函数。因此，C++引入了一个明确的`nullptr`来解决这个问题。

```
read(nullptr); 
```

### 在 Rust 中：

Rust 支持指针，通常称为*原始*指针，但除非需要与 C API 或类似目的进行交互，否则很少使用它们。

指针看起来与 C++ 的类似：

```
// This is a reference coerced to a const pointer
let age: u16 = 27;
let age_ptr: *const u16 = &age;

// This is a mut reference coerced to a mutable pointer
let mut total: u32 = 0;
let total_ptr: *mut u32 = &mut total; 
```

尽管可以在非安全块外创建指针，但你可能想对指针执行的许多函数都是根据定义不安全的，并且必须在`unsafe`块内执行。

完整的文档在[这里](https://doc.rust-lang.org/std/primitive.pointer.html)。

## 参考文献

### 在 C++ 中

引用也是指向地址的变量，但与指针不同，它不能重新赋值，也不能为`NULL`。因此，引用通常被认为比指针更安全。引用仍然可能变得悬空，假设其引用的地址不再有效。

### 在 Rust 中

引用也由编译器进行生命周期跟踪。

## 元组

元组是用括号括起来的值的列表。它们在传递临时或临时数据时很有用，而且你不想为这种情况写一个特殊的结构体。

### 在 C++ 中

C++ 本身不支持元组，但 C++11 提供了一个模板用于像这样传递它们：

```
#include <tuple>

std::tuple<int, int> get_last_mouse_click() {
  return std::make_tuple(100, 20);
}

std::tuple<int, int> xy = get_last_mouse_click();
int x = std::get<0>(xy);
int y = std::get<1>(xy); 
```

### 在 Rust 中

元组是语言的一部分，因此它们更加简洁和易于使用。

```
fn get_last_mouse_click() -> (i32, i32) {
  (100, 20)
}
// Either
let (x, y) = get_last_mouse_click();
println!("x = {}, y  = {}", x, y);
// or
let xy = get_last_mouse_click();
println!("x = {}, y  = {}", xy.0, xy.1); 
```

# 字面量

# 字面量

## 在 C++ 中

### 整数

整数是一个十进制值，后面跟着一个可选的类型后缀。

在 C ++中，[整数字面量](http://en.cppreference.com/w/cpp/language/integer_literal#The_type_of_the_literal)可以仅表示数字，也可以带有后缀。十六进制、八进制和二进制中的值用前缀表示：

```
// Integers
42
999U
43424234UL
-3456676L
329478923874927ULL
-80968098606968LL
// C++14
329'478'923'874'927ULL
// Hex, octal, binary
0xfffe8899bcde3728 // or 0X
07583752256
0b111111110010000 // or 0B 
```

整数上的`u`、`l`和`ll`后缀表示它是`unsigned`、`long`或`long long`类型。`u`和`l`/`ll`可以是大写或小写。通常，`u`必须在大小之前，但 C++14 允许反向顺序。

C++14 还允许在数字中插入单引号作为分隔符 - 这些引号可以出现在任何位置并且被忽略。

### 浮点数

浮点数可以表示整数或小数。

### 布尔值

C/C++中的`bool`字面量是`true`或`false`。

### 字符和字符串

字符字面量由单引号括起来，可选的宽度前缀。前缀`L`表示宽字符，`u`表示 UTF-16，`U`表示 UTF-32。

```
'a'
L'a' // wchar_t
u'\u20AC' // char16_t
U'\U0001D11E' // char32_t 
```

`char`字面量的一个奇特之处是，在 C 中`sizeof('a')`产生`sizeof(int)`，而在 C ++中产生`sizeof(char)`。测试字符字面量的大小并不是一个好主意。

`char16_t`和`char32_t`足以容纳任何 UTF-16 和 UTF-32 代码单元。

字符串是由双引号括起来的字符序列。始终在末尾附加零值终止符。前缀的工作方式与字符字面量相同，但额外添加了一个`u8`类型以指示 UTF-8 编码的字符串。

```
"Hello"
u8"Hello" // char with UTF-8
L"Hello"   // wchar_t
u"Hello"   // char16_t with UTF-16
U"Hello"   // char32_t with UTF-32 
```

### 用户定义的字面量

C++11 引入了[用户定义的字面量](http://en.cppreference.com/w/cpp/language/user_literal)。这些允许整数、浮点数、字符和字符串具有用户定义的类型后缀，由下划线和小写字符串组成。前缀可以充当装饰符或甚至是一个在编译时修改值的常量表达式运算符。

C++14 进一步定义了用于复数和时间单位的用户定义字面量。

查看链接以获取更多信息。

## Rust

## 整数

在 Rust 中，[数字字面量](https://doc.rust-lang.org/reference.html#integer-literals)也可以仅表示数字，也可以带有后缀。十六进制、八进制和二进制中的值也用前缀表示：

```
// Integers
123i32;
123u32;
123_444_474u32;
0usize;
// Hex, octal, binary
0xff_u8;
0o70_i16;
0b111_111_11001_0000_i32; 
```

Rust 中的下划线是一个分隔符，并且与 C++14 中的单引号相同。

### 浮点数

浮点数可以表示整数或小数。与整数一样，它们可以添加后缀以指示它们的类型。

```
let a = 100.0f64;
let b = 0.134f64;
let c = 2.3f32; // But 2.f32 is not valid (note 1)
let d = 12E+99_E64; 
```

浮点数的一个怪癖是小数点用于浮点分配，但它也用于成员和函数调用。所以你不能说`2.f32`，因为它认为你在引用 f32 上的 2。而是语法要求你说`2.f32`或改变你声明类型的方式，例如`let v: f32 = 2.;`。

## 布尔值

布尔字面量只是`true`或`false`。

```
true
false 
```

## 字符和字符串

在 Rust 中，字符是由单引号括起来的任何 UTF-32 代码点。这个值可以转义也可以不转义，因为.rs 文件是 UTF-8 编码的。

特殊前缀`b`可以用来表示字节字符串，即每个字符都是单个字节。

```
'x'
'\'' # Escaped single quote
b'&' # byte character is a u8 
```

字符串是由双引号括起来的字符串文本：

```
"This is a string"
b"This is a byte string" 
```

前缀`b`表示字节字符串，即单字节字符。Rust 允许使用反斜杠符号类似于 C++的反斜杠符号对换行、空格、双引号和反斜杠进行转义。

```
"This is a \
  multiline string"
"This string has a newline\nand an escaped \\ backslash"
"This string has a hex char \x52" 
```

字符串也可以是'原始'的，以避免转义。在这种情况下，字符串前缀为 r，后跟零个或多个井号，双引号中的字符串，以及相同数量的井号来关闭。字节字符串是字符串中未解释的字节值。

```
r##"This is a raw string that can contain \n, \ and other stuff without escaping"##
br##"A raw byte string with "stuff" like \n \, \u and other things"## 
```

# 集合

# 集合

集合是以某种方式保存零个或多个元素的东西，允许你枚举这些元素，添加或删除元素，查找它们等等。

+   Vector - 动态数组。从末尾添加或删除元素很便宜（只要数组足够大以容纳额外的项）。从数组的任何其他部分插入或删除项目更昂贵，涉及内存移动。一般来说，您应该始终为向量保留足够的空间，以容纳您预期的最多元素。重新分配内存可能很昂贵，并导致碎片化。

+   Vecdeque - 环形缓冲数组。可以相对便宜地从任一端添加或删除项目。数组中的项目不是按顺序排列的，因此管理环绕和删除比 Vector 更复杂一些。

+   LinkedList - 链表为每个元素单独分配内存，使得从列表中任何位置添加或删除元素变得便宜。然而，通过索引迭代列表会有更多的开销和更多的堆分配。

+   Set - 保存一组唯一项的集合。插入重复项将不会成功。一些集合保持插入顺序。集合在你想要从输入中消除重复项时很有用。

+   Map - 每个项都由唯一键引用的集合。一些映射可以保持插入顺序。

C++和 Rust 将集合作为其标准库的一部分，这在现代语言中很常见。

| C | C++ | Rust |
| --- | --- | --- |
| - | `std::vector` | `std::vec::Vec`或`std::collections::VecDeque` |
| - | `std::list` | `std::collections::LinkedList` |
| - | `std::set` | `std::collections::HashSet`，`std::collections::BTreeSet` |
| - | `std::map` | `std::collections::HashMap`，`std::collections::BTreeMap` |

C 没有标准的集合类或类型。一些库提供集合 API，比如[glib](https://developer.gnome.org/glib/)或[cii](https://github.com/drh/cii)。

## 迭代器

迭代器是集合中位置的引用，可以逐个元素地遍历集合。

### C++

C++11 提供了一种简便的方式来迭代一个集合：

```
std::vector<char> values;
for (const char &c : values) {
    // do something to process the value in c
} 
```

迭代器在 C++98 及之前更加明确，而在 C++11 中的代码基本上等同于这样：

```
std::vector<char> values;

for (std::vector<char>::const_iterator i = values.begin(); i != values.end(); ++i) {
    const char &c = *i;
    // do something to process the value in c
} 
```

这相当冗长，但基本上每种集合类型都定义了一个可变的`iterator`和一个不可变的`const_iterator`类型，调用`begin`返回集合的起始迭代器。对迭代器调用`++`操作符重载会使其在集合中前进到下一个元素。当它达到`end`返回的排他值时，它已经到达集合的末尾。

显然，对于像`vector`这样的索引类型，你也可以通过索引引用元素，但是对于其他集合类型来说，使用迭代器更有效率。

#### 处理集合

C++提供了一些实用模板，在<algorithm class="hljs-meta">用于在集合中实时修改序列。</algorithm>

### Rust

Rust 也有类似于 C++的迭代器，它们通过集合逐步增加。

待办事项

待办链式迭代器

待办将一个集合映射到另一个集合

# 结构体

# 结构体

## C++

在实现上，C++中的`class`和`struct`基本上是相同的东西。它们都包含字段，并且它们都可以在类（`static`）或实例级别附加方法。

```
class Foo {
public:
   // Methods and members here are publicly visible
   double calculateResult();
protected:
   // Elements here are only visible to ourselves and subclasses
   virtual double doOperation(double lhs, double rhs);
private:
   // Elements here are only visible to ourselves
   bool debug_;
}; 
```

默认的访问级别对于结构体是`public`，对于类是`private`。一些关于模板的规则仅适用于类。

从心理学的角度来看，`struct`倾向于用于保存主要是静态的或传递的公共数据。`class`倾向于更自包含，具有用于访问或管理私有字段的方法。

所以这些是等价的：

```
struct Foo { // as a struct
private:
};

class Foo { // As a class
};

// Or the other way around

struct Bar {
};

class Bar {
public:
}; 
```

类也可以使用访问修饰符从基类继承。因此，当一个类想要那些方法对调用者或子类可见时，类可以指定`public`、`protected`或`private`。

类和结构体可能具有特殊的构造函数和析构函数方法，这些方法在下面的章节中描述。

```
class Size {
public:
  Size(int width, int height);

  int width_;
  int height_;

  int area() const;
}; 
```

然后在.cpp 文件中，你可能会实现构造函数和方法：

```
Size::Size(int width, int height) : width_(width), height_(height) {}

int Size::area() { return width_ * height_; } 
```

## Rust

Rust 仅有结构体。`struct`由一个定义组成，该定义指定字段及其访问级别（公共或否），以及包含与结构体绑定的函数实现的`impl`部分。

```
struct Size {
  pub width: i32;
  pub height: i32;
} 
```

一个`impl`部分跟随其中包含相关函数：

```
impl Size {
  pub fn new(width: i32, height: i32) -> Size {
    Size { width: width, height: height, }
  }

  pub fn area(&self) -> i32 {
    self.width * self.height
  }
} 
```

这里的`new()`函数是一个方便的方法，它返回一个使用提供的参数预初始化的结构体。`area()`函数指定了一个`&self`参数，并返回一个区域计算。任何提供了`&self`或`&mut self`的函数都可以从绑定到结构体的变量中调用。

```
let size = Size::new(10, 20);
println!("Size = {}", size.area()); 
```

`self`关键字的工作方式与 C++中的`this`相似，作为调用函数的结构体的引用。如果函数修改结构体，则必须说明`&mut self`，这表示函数修改结构体。

Rust 中没有继承。相反，一个`struct`可以实现零个或多个 traits。一个 trait 描述了可以与结构体关联的某种行为，并在本章后面进一步描述。

## 构造函数

在 C++ 中，所有类都有隐式或显式构造函数。要么编译器生成它们，要么你自己生成，或者两者兼而有之。

当一个类没有定义自己的默认构造函数、复制构造函数和赋值运算符时，将创建一个隐式默认构造函数、复制构造函数和赋值运算符。我们在第 73 页看到为什么这可能是一个坏消息。

从阅读中变得明显的是 C++ 中存在许多噪音和潜在错误。如果这里使用原始指针而不是`std::unique_ptr`，那么错误可能会更多。

在 Rust 中，事情更简单，我们将看到它如何处理错误。

首先，让我们在 Rust 中声明我们的等效结构体：

```
struct Person {
  pub name: String,
  pub age: i32,
  pub credentials: Option<Credentials>,
} 
```

由于凭据是可选的，我们将其包装在一个`Option`对象中，即凭据可能是`None`，也可能是`Some(Credentials)`。系统中的任何代码都可以通过声明一个实例来实例化一个`Person`：

```
let person = Person { name: String::from("Bob"), age: 20, credentials: None } 
```

在 Rust 中，你不能创建一个未初始化所有成员的结构体，因此我们不能出现我们不知道每个字段中有什么的情况 - 它必须由我们的代码设置。

但是声明结构体有点笨拙，特别是如果结构体在许多地方创建。因此可以编写一个类似于 C++ 中构造函数的函数。

相反，你可以在结构体的实现中实现一个静态方法，返回一个初始化的结构体，例如：

```
impl Person {
  pub fn new(name: String, age: String) -> Person {
    Person { name: name.clone(), age: age, credentials: None }
  }
} 
```

请注意，Rust 不支持重载。因此，如果我们有多个“构造函数”方法，它们每个都必须有唯一的名称。

最后，如果我们想复制`Person`结构体呢？

默认情况下，Rust 不允许在用户定义的结构体上进行复制。将一个变量赋值给另一个变量会移动所有权，而不是复制。

有两种方法使用户定义的结构体可复制

1.  实现`Copy` trait，这意味着��值是隐式的，但这是我们想要的吗？我们真的想无意中复制一个结构体吗？

1.  实现`Clone`而不是添加一个`clone()`方法，并要求显式调用`clone()`来复制结构体的副本。

但是编译器可以派生`clone()`，只要结构体的所有成员实现了 Clone trait。

```
#[derive(Clone)]
struct Person {
  pub name: String,
  pub age: i32,
  pub credentials: Option<Credentials>, // Credentials must implement Clone
}

impl Person {
  pub fn new(name: String, age: String) -> Person {
    Person { name: name.clone(), age: age, credentials: None }
  }
}

//...

let p = Person::new(String::from("Michael"), 20);
let p2 = p.clone(); 
```

我们可以看到 Rust 的构造和`clone()`行为基本上是声明性的。我们看到 C++ 在构造、复制构造和赋值方面有各种规则和细微差别，使其复杂且容易出错。

## 析构函数

C++ 的析构函数是当你的对象超出范围或被删除时调用的专门方法。

```
class MyClass {
public:
  MyClass() : someMember_(new Resource()) {}
  ~MyClass() {
     delete someMember_;
  }

private:
  Resource *someMember_;
} 
```

在 C++ 中，你可以声明一个类的析构函数，在对象即将被销毁时调用。如果你的类继承自另一个类，那么在基类上调用`delete`时，你必须使用虚析构函数。

由于 Rust 不进行继承，也没有构造函数，清理方式不同且更简单。你实现`Drop`特质来代替析构函数。

```
impl Drop for Shape {
    fn drop(&mut self) {
        println!("Shape dropping!");
    }
} 
```

编译器识别该特质。如果你实现了这个特质，那么编译器就知道在销毁结构体之前调用你的`drop()`函数。就这么简单。

偶尔可能有理由在它超出范围之前明确删除一个结构体。也许变量持有的资源应该尽快释放，以释放一个处于争用状态的资源。无论原因是什么，答案是像这样调用`drop`：

```
{
  let some_object = SomeObject::new();
  //...
  // Ordinarily some_object might get destroyed later,
  // but this makes it explicitly happen here
  drop(some_object);
  //...
} 
```

## 访问限定符规则

C++类可以使用 public、private 和 protected 关键字向任何其他类或从自身继承的东西隐藏或显示方法和成员：

+   `public` – 可被类内或类外的任何代码所见。

+   `private` – 只能被类内部的代码使用。甚至子类也无法访问这些成员。

+   `protected` – 可被类内部的代码和子类使用。

一个类可以将另一个函数或类指定为友元，以访问类的私有和受保护成员。

Rust 使事情变得有些简单。

如果你想让一个结构体在你的模块外可见，你就标记它为`pub`。如果你不标记它为`pub`，那么它只能在模块和子模块内可见。

```
pub struct Person { /* ... */ } 
```

如果你想公开访问结构体的成员（包括修改它如果它是可变的），那么标记它为`pub`。

```
pub struct Person {
  pub age: u16,
} 
```

如果你想让某些东西能够调用你的结构体上的函数，你就标记它为`pub`。

```
impl Person {
  pub fn is_adult(&self) -> bool {
    self.age >= 18
  }
} 
```

## 函数

函数可以绑定到`impl`块中的结构体内部：

```
impl Shape {
  pub fn new(width: u32, height: u32) -> Shape {
    Shape { width, height }
  }

  pub fn area(&self) -> i32 {
    self.width * self.height
  }

  pub fn set(&mut self, width: i32, height: i32) {
    self.width = width;
    self.height = height;
  }
} 
```

以`&self` / `&mut self`参数开头的函数绑定到实例。没有这些参数的绑定到类型。因此，`new()`函数可以被称为`Shape::new()`。

当提供`&self`时，函数在实例上被调用。所以例如：

```
let shape = Shape::new(100, 100);
let area = shape.area(); 
```

当提供`&mut self`时，表示该函数会改变结构体的内容。

与 C++不同，对结构体的所有访问都必须有资格。在 C++中，你不必说`this->foo()`来从类的另一个成员调用 foo()。Rust 要求代码明确地说`self.foo()`。

## 静态函数

静态函数只是在`impl`块中没有`&self`或`&mut self`作为其第一个参数的函数，例如。

```
impl Circle {
   fn pi() -> f64 { std::f64::consts:PI }
}
//...
let pi = Circle::pi(); 
```

换句话说，它们不是绑定到类型的实例，而是绑定到类型本身。例如，`Circle::pi()`。

## 特质

C++允许一个类从另一个类继承。一般来说，这是一个有用的功能，尽管如果你实现了多重继承，特别是可怕的菱形模式，它可能会变得非常复杂。

正如我们所发现的，Rust 根本没有类 - 它们是绑定函数的结构体。那么你如何继承代码呢？答案是你不继承。

相反，您的结构体可能实现了一些像部分类的特征。

一个 trait 的声明如下：

```
trait HasCircumference {
  fn circumference(&self) -> f64;
} 
```

这里的 trait `HasCircumference` 有一个名为 `circumference()` 的函数，其签名已定义但必须实现。

一个类型可以通过声明和 `impl` 来实现该 trait。

```
impl HasCircumference for Size {
  fn circumference(&self) -> i32 {
    2.0 * std::f64::consts::PI * self.radius
  }
} 
```

一个 trait 可以提供默认的函数实现。例如，`HasDimensions` trait 可以实现 `area()` 来避免实现者的麻烦。

```
trait HasDimensions {
  fn width(&self) -> u32;
  fn height(&self) -> u32;

  fn area(&self) -> u32 {
    self.width() * self.height()
  }
} 
```

## 生命周期

在 C++ 中，一个对象从被构造的那一刻开始存在，直到被析构的那一刻结束。

如果您在堆栈上声明对象，那么该生命周期是隐式的。对象将随着其进入和离开作用域而创建 / 销毁。如果您的对象是另一个对象的成员，则它也是隐式的 - 生命周期在包含对象中，以及包含对象中其他成员的声明顺序。

但是，如果您通过 `new` 分配对象，那么您可以在何时 `delete` 是由您决定的。如果您过早地 `delete`，或者忘记 `delete`，那么您可能会使您的程序不稳定。C++ 鼓励使用智能指针来管理对象的生命周期，将其绑定到智能指针本身的隐式生命周期 - 当智能指针被销毁时，它会删除所持有的指针。一种更复杂的智能指针允许同一指针的多个实例同时存在，并且引用计数用于当最后一个智能指针被销毁时销毁指针。

即便如此，C++ 并不关心你是否用一个不再存在的引用或指针初始化了一个类。如果你这样做了，你的程序将崩溃。

让我们编写一个 `Incrementor` 类，它会增加一个整数值并返回该值。

```
class Incrementor {
public:
    Incrementor(int &value) : value_(value) {}
    int increment() { return ++value_; }

private:
    int &value_;
}; 
```

这看起来没问题，但如果我们这样使用它呢？

```
Incrementor makeIncrementor() {
  // This is a bad idea
    int value = 5;
    return Incrementor(value);
} 
```

这段代码将一个`int`的引用传递给了类构造函数，并从函数本身返回了`Incrementor`。但是当调用`increment()`时，引用是悬挂的，任何事情都可能发生。

## Rust 生命周期

Rust *确实* 关心对象的生命周期，并跟踪它们以确保您不能引用不存在的东西。大多数情况下，这是自动的，并且可以从您尝试坏事时收到的错误消息中明显看出。

编译器还实现了一个 *借用检查器*，用于跟踪对对象的引用，以确保：

1.  引用的持有时间不会超过它们所引用的对象的生命周期。

1.  一次只能有一个可变引用，不能与不可变引用同时存在。这是为了防止数据竞争。

如果编译器发现代码违反了其规则，它将生成编译错误。

所以让我们写一个与上面的 `Incrementor` 等效的 Rust 代码。Rust 代码将持有一个整数 `i32` 的引用，并从一个绑定函数中递增它：

```
struct Incrementor {
  value: &mut i32
}

impl Incrementor {
  pub fn increment(&mut self) -> i32 {
    *self.value += 1;
    *self.value
  }
} 
```

看起来没问题，但我们得到的第一个错误是：

```
2 |   value: &mut u32
  |          ^ expected lifetime parameter 
```

我们尝试创建一个管理引用的结构体，但编译器对这个引用的生命周期一无所知，因此它生成了一个编译错误。

为了帮助编译器解决它的问题，我们将用一个生命周期来注释我们的结构体，我们将其称为 `'a`。标签可以是任何你喜欢的东西，但通常它会是一个字母。

这个生命周期标签是我们结构体的一个提示，它表示我们在结构体内部使用的引用必须至少具有与结构体本身一样长的生命周期 - 即 `Incrementor<'a>` 和 `value: &'a mut i32` 共享相同的生命周期约束，编译器会强制执行它。

```
struct Incrementor<'a> {
  value: &'a mut i32
}

impl <'a> Incrementor<'a> {
  pub fn increment(&mut self) -> i32 {
    *self.value += 1;
    *self.value
  }
} 
```

有了注释，我们现在可以使用这段代码：

```
let mut value = 20;
let mut i = Incrementor { value: &mut value };
println!("value = {}", i.increment()); 
```

注意注释 `'a` 可以是我们喜欢的任何标签 - 如果我们愿意，`'increment` 就可以工作，但显然它更冗长。

有一个特殊的生命周期称为 `'static`，它指的是像静态字符串和函数这样的东西，它们的生命周期与运行时一样长，因此可以假定它们总是存在的。

### 生命周期省略

Rust 允许在大多数函数签名中省略引用生命周期。

基本上，它假定当将引用传递到函数中时，引用的生命周期隐式长于函数本身，因此不需要注释。

```
fn find_person(name: &str) -> Option<Person>
// instead of
fn find_person<'a>(name: &'a str) -> Option<Person> 
```

省略规则在进一步的参考链接中有描述。

### 进一步的参考资料

生命周期是一个庞大的主题，文档在[这里](https://doc.rust-lang.org/book/second-edition/ch10-03-lifetime-syntax.html#lifetime-elision)。

# 注释

# 注释

Rust 注释与 C++ 类似，只是它们可能包含 Unicode，因为 .rs 文件是 UTF-8 编码的：

```
/*
 This is a comment
*/

// This a comment with Unicode, 你好 
```

但是，除了使用三斜杠 `///` 注释的内容外，还可以通过一个名为 `rustdoc` 的工具来解析产生文档：

```
/// This is a comment that becomes documentation for do_thing below
pub fn do_thing() {}
/// Returned by server if the resource could not be found
pub const NOT_FOUND = 404; 
```

运行 `cargo doc` 在项目上会产生 HTML 文档，其中包含文件中的注释。

注释以 Markdown 格式编写。这意味着你有一种可读的人类语言来编写丰富的文本文档，如果不够用，你可以通过标签回到 HTML。

请参阅[完整文档](https://doc.rust-lang.org/book/documentation.html)

# 生命周期、引用和借用

# 生命周期、引用和借用

当你将一个对象分配给 Rust 中的一个变量时，你被称为绑定它。也就是说，只要它在范围内，你的变量就“拥有”该对象，当它超出范围时，它就被销毁了。

```
{
  let v1 = vec![1, 2, 3, 4]; // Vec is created
  ...
} // v1 goes out of scope, Vec is dropped 
```

因此变量是有范围的，范围是影响它们生命周期的约束。在范围之外，变量无效。

在这个例子中，重要的是记住 `Vec` 在堆栈上，但它分配用于保存其元素的指针在堆上。当 `Vec` 被丢弃时，堆空间也将被回收。

如果我们将 v1 分配给另一个变量，那么所有对象的所有权都将移动到该其他变量：

```
{
  let v1 = vec![1, 2, 3, 4];
  let v2 = v1;
  ...
  println!("v1 = {:?}", v1); // Error!
} 
```

这可能看起来很奇怪，但值得记住 C++ 中出现的一个严重问题，即复制构造函数错误。很容易复制一个类并无意中在多个实例之间共享私有数据或状态。

我们不希望对象 v1 和 v2 共享内部状态，在 Rust 中它们不会。Rust 将数据从 v1 移动到 v2，并标记 v1 为无效。如果你尝试在代码中再次引用 v1，它将生成一个编译错误。这个编译错误将指示所有权已转移到 v2。

同样，如果我们将值传递给函数，那也会移动所有权：

```
{
  let v1 = vec![1, 2, 3, 4];
  we_own_it(v1);
  println!("v = {:?}", v1);
}

fn we_own_it(v: Vec<i32>) {
  // ...
} 
```

当我们调用 we_own_it() 时，我们将对象的所有权移交给了函数，它��也没有返回。因此，使用 v1 进行的以下调用是无效的。我们可以调用一个名为 we_own_and_return_it() 的函数的变体，它确实返回所有权：

```
v1 = we_own_and_return_it(v1)
...
fn we_own_and_return_it(v: Vec<i32>) -> Vec<i32> {
  // ...
  v1
} 
```

但这很混乱，下一节中有一种更好的方法称为借用。

这些移动赋值看起来很奇怪，但这是 Rust 保护你免受 C++ 中常见的复制构造函数错误的方式。如果你将一个不可复制的对象从一个变量赋给另一个变量，你会移动所有权，旧变量将无效。

如果你真的想将对象从一个变量复制到另一个变量，使两者持有独立的对象，你必须使你的对象实现 Copy trait。通常最好实现 Clone trait，它通过一个显式的 clone() 操作方式工作。

## 变量必须绑定到某个东西

另一个要点。变量必须绑定到某个东西。如果一个变量没有被初始化为某种值，你就不能使用它：

```
let x: i32;
println!("The value of x is {}", x); 
```

在 C++ 中，声明变量并不对其进行任何操作是完全有效的。或者有条件地对变量进行一些操作，这会让编译器困惑，因此它只会生成一个警告。

```
int result;
{
   // The scope is to control the lifetime of a lock
   lock_guard<mutex> guard(data_mutex);
   result = do_something();
}
if (result == 0) {
  debug("result succeeded");
} 
```

Rust 编译器会抛出一个错误，而不是警告，如果变量未初始化。如果你声明一个变量但最终没有使用它，它也会警告你。

## 引用和借用

我们已经看到对象的所有权是由编译器跟踪的。如果你将一个变量赋给另一个变量，对象的所有权被认为已转移到被赋值的变量。原始变量将无效，如果使用它，编译器将生成错误。

不幸的是，这也适用于将值传递给函数，这是一个麻烦。但是变量绑定可以被借用。如果你希望将一个变量借给一个函数使用，你可以传递一个对象的引用：

```
{
  let mut v = Vec::new(); // empty vector
  fill_vector(&mut v);
  // ...
  println!("Vector contains {:?}", v);
}
//...
fn fill_vector(v: &mut Vec<i32>) {
  v.push(1);
  v.push(2);
  v.push(3);
} 
```

在这里，我们创建了一个空向量，并将一个可变引用传递给一个名为 fill_vector() 的函数。编译器知道该函数正在借用 v，然后在函数返回后将所有权返回给 v。

# 表达式

# 表达式

表达式是一个会评估为某个值的东西。就像 C++ 差不多...

```
let x = 5 + 5; // expression evaluates to 10 
```

## 但块也是表达式

更有趣的是，由花括号表示的代码块也会评估为一个表达式。这是合法的代码：

```
let x = {};
println!("x = {:?}", x); 
```

x 被分配了什么？在这种情况下，该块为空，所以 x 被赋予了`()`的值。值`()`是一种特殊的单元类型，基本上意味着既不是是也不是。它只是意味着"值"。这是任何函数或类型的默认类型。它的工作方式有点像 C++中的`void`，意味着值是没有意义的，所以甚至不要看它。

```
x = () 
```

该块还返回了一个`()`的值。

```
let x = { println!("Hello"); };
println!("x = {:?}", x); 
```

同样，这是因为尽管该块执行某些操作（打印 Hello），但它不会评估为任何内容，因此编译器为我们返回了`()`。

到目前为止，还是毫无用处。但是我们可以改变块表达式的评估结果：

```
let x = {
    let pi = 3.141592735;
    let r = 5.0;
    2.0 * pi * r
};
println!("x = {}", x); 
```

现在 x 被分配了最后一行的结果，这是一个表达式。请注意，该行没有用分号终止。这成为了块表达式的结果。如果我们在那一行的末尾放置了一个分号，就像我们用 println！("Hello")一样，表达式将评估为()。

### 在函数中使用

简单函数只需省略 return 语句：

```
pub fn add_values(x: i32, y: i32) -> i32 {
  x + y
} 
```

### 您也可以在块中使用 return

有时您可能需要显式使用 return 语句。块表达式在块末尾评估，因此如果您需要提前退出，只需使用 return。

```
pub fn find(value: &str) -> i32 {
  if value.len() == 0 {
    return -1;
  }
  database.do_find(value)
} 
```

### 简化 switch 语句

在 C 或 C++中，您经常会看到这样的代码：

```
std::string result;
switch (server_state) {
  case WAITING:
    result = "Waiting";
    break;
  case RUNNING:
    result = "Running";
    break;
  case STOPPED:
    result = "Stopped";
    break;
  }
} 
```

该代码想要测试 server_state 中的值并将一个字符串分配给 result。除了看起来有点笨拙之外，它还引入了错误的可能性，因为我们可能会忘记分配，或者添加一个 break，或者省略其中一个值。

在 Rust 中，我们可以直接将结果分配给 match 的 result，因为每个 match 条件都是一个块表达式。

```
let result = match server_state {
    ServerState::WAITING => "Waiting",
    ServerState::RUNNING => "Running",
    ServerState::STOPPED => "Stopped",
}; 
```

不仅长度减半了，而且还减少了错误的范围。编译器将块表达式的值分配给变量 result。它还将检查每个匹配块返回相同类型的类型（因此您不能从一个匹配中返回一个浮点数，而从其他匹配中返回字符串）。如果 ServerState 枚举具有我们的匹配没有处理的其他值，它还将生成错误。

### 三元运算符

C/C++中的三元运算符是执行 if/else 表达式条件的一种缩写方式，通常用于将结果分配给变量。

```
bool x = (y / 2) == 4 ? true : false; 
```

Rust 没有三元运算符的等价物，但可以使用块表达式来实现。

```
let x = if y / 2 == 4 { true } else { false }; 
```

与 C/C++不同，您可以添加额外的 else if、匹配项或任何其他内容，只要每个分支返回相同的类型。

# 条件

# 条件

C++和 Rust 之间的条件代码类似。您测试表达式的布尔真值，并且可以使用布尔运算符（例如&&和||）将表达式连接在一起。

```
int x = 0;
while (x < 10) {
  x++;
}
int y = 10;
bool doCompare = true;
if (doCompare && x == y) {
  printf("They match!\n");
} 
```

在 Rust 中：

```
let mut x = 0;
while x < 10 {
  x = x + 1;
}
let y = 10;
let do_compare = true;
if do_compare && x == y {
  println!("They match!");
} 
```

最显着的区别是 Rust 省略了外部大括号，所以代码稍微清晰一些。您不必省略外部大括号，但是如果您将它们保留下来，编译器将发出警告。

## 三元运算符

三元运算符是 C++中用于简单条件的特殊? : 缩写符号。

```
int x = (y > 200) ? 10 : 0; 
```

Rust 不支持这种记法，不过你可以利用块的求值作为表达式来表达这个意思：

```
let x = if y > 200 { 10 } else { 0 }; 
```

基本上，你可以使用 if 和 else 来进行一行条件赋值。还要注意，如果你愿意，甚至可以加入一两个 "else if"：

```
let c = get_temperature();
let water_is = if (c >= 100) { "gas" } else if (c < 0) { "solid" } else { "liquid" }; 
```

## 条件 "if let"

一个不寻常的特性是 "if let" 模式。这将一个测试与一个模式匹配，并在匹配时自动将结果分配给元组。它最常见于返回枚举值的代码，如 `Result` 或 `Option`。

例如：

```
fn search(name: &str) -> Option<Person> { /* ... */ }
//...
if let Some(person) = search("fred") {
  println!("You fould a person {}", person);
}
else {
  println!("Could not find person");
} 
```

# Switch / Match

# Switch / Match

## C++

在 C 或 C++ 中，`switch` 语句允许将条件或变量与一系列值进行比较，并根据结果执行与这些值相关联的代码。还有一个默认子句匹配任何未被明确捕获的值。

```
int result = http_get();
switch (result) {
case 200:
  success = true;
  break;
case 404:
  log_error(result);
  // Drop through
default:
  success = false;
  break;
} 
```

switch 语句可能会引发错误，因为当没有提供 `default` 子句时，行为是未定义的。当意外地忘记了 `break` 语句时，也可能会引发错误。在上面的示例中，代码明确地从 404 处理程序 "掉入" 到默认处理程序。只要不是有人在 404 和默认之间插入一些额外的子句，这段代码就能正常工作...

此外，switch 语句仅适用于数值（或 `bool`）。

## Rust

[Match](https://doc.rust-lang.org/book/match.html) 就像是一个强化版的 `switch` 语句。

在 C++ 中，switch 是对某种整数值（包括字符和枚举）与一系列值进行直接比较。如果比较成功，紧邻它的代码将执行，直到 switch 语句的底部或达到一个 break。

TODO

# 转换

# 转换

转换是将一种类型强制转换为另一种类型，或者动态地在另一种类型中生成等效值的行为。

C++ 有一系列的转换操作符，可以将一种类型的指针或值转换为另一种类型的指针或值。

+   `const_cast<T>(value)` - 移除值的常量限制，以便可以修改。

+   `static_cast<T>(value)` - 尝试使用隐式和用户定义的转换在类型之间转换。

+   `reinterpret_cast<T>(value)` - 一个编译器指令，只是将输入视为其他类型。它不涉及任何形式的转换。

+   `dynamic_cast<T>(value)` - 尝试将类指针/引用转换为其继承层次结构中的其他类的指针/引用。涉及运行时检查。

+   传统的 C 风格转换 - C++ 编译器将尝试将其解释为 `const_cast`、`static_cast` 和 `reinterpret_cast` 的组合。

这只是对转换的一个非常简短的总结，可能会引发比解答更多的问题。在 C++ 中，转换非常复杂而微妙。有些转换仅仅是指示编译器忽略 const 或将一种类型视为另一种类型。静态转换可能涉及代码生成以转换类型。动态转换可能添加运行时检查并抛出异常。

Rust 没有与此复杂性相当的东西。可以使用 [`as`](https://doc.rust-lang.org/book/casting-between-types.html#as) 关键字将数字类型转换为另一种数字类型。

```
let a = 123i32;
let b = a as usize; 
```

超出这个范围的任何事情都需要实现 `Into<>` 或 `From<>` 特性，并将转换作为显式操作。

编译器也不允许代码去除 `const` 或将一个类型视为另一个类型，除非通过 `unsafe` 代码块。

# 转换

Rust 允许一些类型[转换](https://doc.rust-lang.org/book/casting-between-types.html#transmute)为其他类型。转换是一种 `unsafe` 操作，但它允许将一个内存位置视为另一种类型，例如将字节数组视为整数。

# 枚举

# 枚举

在 C++ 中，`enum` 是一组被赋予 `int` 值的标签。即它基本上是一组具有标量值的常量。

```
enum HttpResponse {
  okay = 200,
  not_found = 404,
  internal_error = 500,
}; 
```

C++11 对此概念进行了一点扩展，允许你声明一个使用另一种整数类型的 `enum`，例如，一个 `char` 来保存值。

```
enum LibraryCode : char {
  checked_in = 'I',
  checked_out = 'O',
  checked_out_late = 'L'
}; 
```

在 Rust 中，[`enum`](https://doc.rust-lang.org/book/enums.html) 可以像在 C++ 中一样是标量值。

```
enum HttpResponse {
  Ok= 200,
  NotFound= 404,
  InternalError = 500
}; 
```

但是枚举也可以保存实际数据，因此你可以传达比静态值本身更多的信息。

```
enum HttpResponse {
  Ok,
  NotFound(String),
  InternalError(String, String, Vec<u8>)
} 
```

你也可以将函数绑定到枚举上：

```
impl HttpResponse {
  pub fn code(&self) => {
    match *self {
      HttpResponse::Ok => 200,
      HttpResponse::NotFound(_) => 404,
      HttpResponse::InternalError(_, _, _) => 500,
    }
  }
} 
```

因此，我们可能有一个函数，它发出一个 http 请求并返回一个响应：

```
fn do_request(url: &str) -> HttpResponse {
  if url == "/invalid" {
    HttpResponse::NotFound(url.to_string())
  }
  else {
    HttpResponse::Ok
  }
}
//...
let result = do_request("/invalid");
if let HttpResponse::NotFound(url) = result {
  println!("The url {} could not be found", url);
} 
```

现在我们的代码能够以枚举返回更有意义的响应，代码能够提取出这些响应并打印出有用的信息。

# 循环

# 循环

## C++

### For 循环

C/C++ 中的 `for` 循环由包含在 `for()` 区域中的 3 个表达式部分和一段要执行的代码块组成：

for 语句的三个部分允许： 

+   零个或多个要初始化的变量（可以为空）

+   零个或多个条件必须为真以使循环继续（可以为空）

+   零个或多个在每次迭代中执行的操作（可以为空）。

因此，这是一个有效的 for 循环：

```
// Infinite
for (;;) {
  //...
} 
```

这样也可以：

```
for (int i = 10, j = 0; (j = i * i) <= 100; i--) {
  //...
} 
```

这显然是一个复杂而有些混乱的循环，因为它将赋值和条件测试混合到了终止文本中，但这是完全合法的。

#### 遍历一个范围

C++ 循环由一个初始化表达式、一个条件表达式和一个循环表达式组成，用分号分隔。因此，一个从 0 到 100 迭代的循环如下所示：

```
for (int i = 0; i < 100; i++ ) {
  cout << "Number " << i << endl;
} 
```

#### 遍历 C++ 集合

C++ 引入了迭代器的概念到其集合类中。`iterator` 是可以递增或递减以遍历集合的东西。

因此，为了遍历一个集合从一端到另一端，一个迭代器被赋值为集合的 `begin()` 迭代器，并递增直到匹配 `end()` 迭代器。

```
for (std::vector<string>::const_iterator i = my_list.begin(); i != my_list.end(); ++i ) {
  cout << "Value = " << *i << end;
} 
```

C++11 提供了一种新的基于范围的 for 循环，用于在数组和集合上进行迭代时具有更简单的语法：

```
std::vector values;
...
for (const auto & v: values) {
  ...
}

int x[5] = { 1, 2, 3, 4, 5 };
for (int y : x) {
  ...
} 
```

### 无限循环

无限循环是永远不会结束的循环。在 C++ 中通常的做法是测试一个总是评估为 true 的表达式或使用一个空的 for 循环：

```
while (true) {
  poll();
  do_work();
}
// Or with a for loop
for (;;) {
  poll();
  do_work();
} 
```

### While 循环

C++有条件的`while() {}`和`do { } while()`形式。前者在运行之前测试表达式，而后者在测试表达式之前至少运行一次。

```
while (!end) {
  std::string next = getLine();
  end = next == "END";
} 
```

C++中的 do-while 形式会至少执行一次循环体，因为条件仅在每次迭代后测试，而不是之前。

```
int i = 0;
do {
  i = rand();
} while (i < 20); 
```

### 中断和继续

如果需要提前退出循环或开始下一次迭代，则使用`break`和`continue`关键字。break 关键字终止循环，而 continue 导致循环继续到下一次迭代。

```
bool foundAdministrator = false;
for (int i = 0; i < loginCredentials; ++i) {
   const LoginCredentials credentials = fetchLoginAt(i);
   if (credentials.disabled) {
     // This user login is disabled so skip it
     continue;
   }
   if (credentials .isAdmin) {
     // This user is an administrator so no need to search rest of list
     foundAdministrator = true;
     break;
   }
   // ... 
} 
```

## Rust

### For 循环

Rust 的`for`循环实际上是对迭代器的一种糖。如果结构化类型实现了特性`IntoIterator`，它就可以使用`for`循环进行迭代。

基本上在伪代码中，循环会转化为以下形式：

```
If structure type can be turned `IntoIterator`
  Loop
   If let Some(item) = iterator.next() {
     do_action_to_item(item)
   Else
     break;
  End
Else 
  Compile Error
Done 
```

#### 迭代范围

Rust 中的`Range`对象表示为`from..to`，其中`from`和`to`是值或求值为值的表达式。

例如：

```
let range=0..33;
// Variables
let min = 0;
let max = 100;
let range2 = min..max; 
```

范围是包含/排除的，即最小值包含在`Range`中，但最大值是排除的。

这是一个简单的循环，从 0 到 9 计数

```
for i in 0..10 {
  println!("Number {}", i);
} 
```

值`0..10`是一个从 0 到不包括 10 的`Range`。范围实现了`Iterator`特性，因此 for 循环每次前进一个元素直到达到末尾。

迭代器有很多函数可以执行各种花式操作，但在循环中有一个有用的函数是`enumerate()`函数。它将迭代器转换为返回包含索引和值的元组，而不仅仅是值。

所以例如：

```
for (i, x) in (30..50).enumerate() {
   println!("Index {} is value {}", i, x);
} 
```

### For 循环-迭代数组和集合

这是一个迭代数组的循环：

```
let values = [2, 4, 6, 7, 8, 11, 33, 111];
for v in &values {
   println!("v = {}", v);
} 
```

注意，只能通过引用迭代数组，因为按值迭代会破坏数组。

我们可以直接使用数组和集合实现的`iter()`函数，该函数通过引用工作：

```
let values = vec![2, 4, 6, 7, 8, 11, 33, 111];
for v in values.iter() {
   println!("v = {}", v);
} 
```

如果集合是映射，则迭代器将返回键和值元组

```
use std::collections::HashMap;

let mut values = HashMap::new();
values.insert("hello", "world");
//...
for (k, v) in &values {
  println!("key = {}, value = {}", k, v);
} 
```

另一种迭代的方法是直接在迭代器上使用`for_each()`函数：

```
let values = [2, 4, 6, 7, 8, 11, 33, 111];
values.iter().for_each(|v| println!("v = {}", v)); 
```

### 中断和继续

Rust 还有`break`和`continue`关键字，它们的操作方式类似-它们作用于最内层的循环。`continue`将从下一次迭代开始，而`break`将终止循环。

```
let values = vec![2, 4, 6, 7, 8, 11, 33, 111];
for v in &values {
  if *v % 2 == 0 {
    continue;
  }
  if *v > 20 {
    break;
  }
  println!("v = {}", v);
} 
```

#### 标签

`break`和`continue`默认在当前循环上工作。有时您打算中断外部循环。对于这些情况，您可以为循环加标签，并将该标签传递给`break`或`continue`：

```
'x: for x in 0..10 {
  'y: for y in 0..10 {
     if x == 5 && y == 5 {
       break 'x;
     }
     println!("x = {}, y = {}", x, y);
  }
} 
```

### 无限循环

Rust 有一个明确的无限`loop`，会无限期地运行：

```
loop {
  poll();
  do_work();
} 
```

Rust 建议在需要无限循环以辅助代码生成时使用此形式。请注意，仍然可以使用`break`语句中断无限循环。

### While 循环

Rust 中的`while`循环看起来与 C/C++中的循环很相似。主要区别在于在条件测试周围不需要括号。

```
while request_count < 1024 {
  process_request();
  request_count = request_count + 1;
} 
```

Rust 没有等价于 do-while 循环形式的语法。它可以模拟，但看起来有点不太优雅：

```
let mut i = 0;
loop {
  i = i + 1;
  if i >= 20 { break; }
} 
```

### While let 循环

正如有 `if let` 用于测试和分配与模式匹配的值一样，还有一个等价的 `while let`：

```
let mut iterator = vec.into_iter();
while let Some(value) = iterator.next() {
  process(value);
} 
```

当迭代器返回 `None` 时，此循环将中断。

# 函数

# 函数

在 C++ 中，函数的标准形式是这样的：

```
// Declaration
int foo(bool parameter1, const std::string &parameter2);

// Implementation
int foo(bool parameter1, const std::string &parameter2) {
  return 1;
} 
```

通常情况下，你会声明函数，要么是在源文件中的前向引用，要么是在头文件中。然后你会在源文件中实现函数。

如果函数不返回任何东西，返回类型是 `void`。如果函数确实返回某些东西，则应该对函数内的每个退出分支都有返回语句。

你可以在两种情况下放弃函数声明：

1.  如果函数是内联的，即以 `inline` 关键字为前缀。在这种情况下，函数的整体在一个地方声明和实现。

1.  如果函数不是内联的，但是在同一源文件中调用它的代码之前声明。所以如果上面的函数 `foo` 只被一个源文件使用，那么将实现放入源文件中也将起到声明的作用。

在 Rust 中，与上面的 `foo` 等价的是这样的：

```
fn foo(parameter1: bool, parameter2: &str) -> i32 {
  // implementation
  1
} 
```

实现 *就是* 声明，两者之间没有区别。返回空值的函数省略了 `->` 返回部分。函数也可以在调用它的任何地方之前或之后声明。默认情况下，函数对实现它的模块（和子模块）私有，但将其设置为 `pub fn` 将其暴露给其他模块。

与 C++ 类似，函数必须对每个退出分支进行评估，但这是强制性的。

还请注意，`return` 关键字通常是不必要的。这是一个将两个值相加并无需返回的函数示例：

```
fn add(x: i32, y: i32) -> i32 {
  x + y
} 
```

为什么没有 `return`？正如我们在表达式部分看到的，如果我们从末尾省略分号，那么块将计算出一个值，所以 `x + y` 是函数块求值的结果，并成为我们返回的结果。

有时你明确需要 `return` 关键字。如果你想在函数块结束之前退出函数，你通常这样做：

```
fn process_data(number_of_times: ui32) -> ui32 {
  if number_of_times == 0 {
    return 0;
  }
  let mut result : ui32 = 0;
  for i in number_of_times {
    result += i;
  }
  result
} 
```

## 可变参数

C++ 函数可以使用 ... 省略符号模式获取可变数量的参数。这在诸如 print、scanf 等函数中使用。

```
void printf_like(const char *pattern, ...); 
```

Rust 不支持变长参数函数（这种能力的花哨名称）。但是如果值相同，你可以将额外的参数传递为数组切片，或者作为字典或其他方式。

TODO Rust 数组切片示例

另一种选择是将代码编写为宏。宏可以接受任意数量的表达式，因此你可以编写接受可变参数的代码。这就是 `println!`、`format!` 和 `vec!` 等宏的工作原理。

## 默认参数

C++ 参数可以有默认值。

```
std::vector<Record> fetch_database_records(int number_to_fetch = 100); 
```

函数定义了其名称、它接受的类型以及它返回的值（如果有）。

## 函数重载

C++ 函数可以重载，例如：

```
std::string to_string(int x);
std::string to_string(float x);
std::string to_string(bool x); 
```

Rust 不支持重载。作为替代，每个函数的变体都必须被唯一命名。

## C++11 的替代语法

C++11 引入了一种风格稍微接近 Rust 的新语法。

```
auto function_name(type parameter1, type parameter2, ...) -> return-type; 
```

这种形式是为了让 C++函数声明在某些情况下更接近于 lambda 函数，并帮助处理 decltype 返回值而创建的。

# 多态性

# 多态性

## C++

C++有 4 种类型的多态性：

1.  函数名重载 - 多个定义相同函数，接受不同参数。

1.  强制转换 - 隐式类型转换，例如将 double 赋给 int 或 bool。

1.  参数化 - 模板中参数的编译时替换

1.  包含 - 将具有虚方法的类子类型化会重载它们的功能。你的代码可以使用基类的指针，但当你调用方法时，你调用的是子类型实现的函数。

也就是说，同名函数可以用不同的参数进行重载。

### 函数名重载

```
class Variant {
public:
  void set(); // Null variant
  void set(bool value);
  void set(int value);
  void set(float value);
  void set(Array *value);
}; 
```

从上面的例子中你可能开始看到的一个最大问题是，很容易无意中调用错误的函数，因为 C++也会隐式转换类型。此外，C++还具有默认参数值和默认构造函数。因此，在编译器解析后，你可能调用一个签名的函数，但实际上调用的是完全不同的东西。

```
 // Sample code
Variant v;
//...
v.set(NULL); 
```

这个例子将调用整数重载，因为`NULL`评估为 0。`C++11`的一个变化是引入了一个明确的`nullptr`值和类型，以避免这些问题。

## Rust

Rust 对多态性的支持有限。

1.  函数名重载 - 没有。查看下面的替代方案。

1.  强制转换。Rust 允许使用`as`关键字在数值类型之间进行有限的显式强制转换。否则，查看下面关于`Into`和`From`特性的用法。

1.  参数化 - 与 C++类似，通过泛型

1.  包含 - Rust 中没有继承。在 Rust 中最接近虚方法的东西是一个具有实现函数的特性，一个实现可以用自己的函数覆盖。然而，这种覆盖是在编译时进行的。

### 函数名重载的替代方案

如果你有几个函数，你可以简单地将它们区分开，例如

```
fn new(name: &str) -> Foo { /* ... */ }
fn new_age(name: &str, age: u16) -> Foo { /* ... */ } 
```

#### 使用特性

一种常见的多态性方式是使用*特性*。

有两种标准特性用于此目的：

+   `From<>`特性将某种类型转换为我们的类型。

+   `Into<>`特性将某种类型（在过程中消耗它）转换为我们的类型

你只需要实现`From`或`Into`，因为一个暗示着另一个。

`From`特性更容易实现：

```
use std::convert::From;

impl From<&'static str> for Foo {
  fn from(v: &'static str) -> Self {
    Foo { /* ... */ }
  }
}

impl From<(&'static str, u16)> for Foo {
  fn from(v: (&'static str, u16)) -> Self {
    Foo { /* ... */ }
  }
}
//...

let f = Foo::from("Bob");
let f = Foo::from(("Mary", 16)); 
```

但假设我们想要在类型`Foo`上有一个显式的`new`构造函数。在这种情况下，我们可以使用`Into`特性来编写它：

```
impl Foo {
  pub fn new<T>(v: T) -> Foo where T: Into<Foo> {
    let result = Foo::foo(v);
    // we could code here that we do here after making Foo by whatever means
    result
  }
} 
```

由于`From`暗示了`Into`，我们可以这样调用构造函数：

```
let f = Foo::new("Bob");
let f = Foo::new(("Mary", 16)); 
```

如果你愿意，你可以实现`Into`，但这更棘手，因为它消耗了输入，这可能不是你想要的。

```
// This Into works on a string slice
impl Into<Foo> for &'static str {
    fn into(self) -> Foo {    
        //... constructor
    }    
}

// This Into works on a tuple consisting of a string slice and a u16
impl Into<Foo> for (&'static str, u16) {    
    fn into(self) -> Foo {    
        //... constructor
    }    
}

//...
let f: Foo = "Bob".into();
let f: Foo = ("Mary", 16).into();
// OR
let f = Foo::new("Bob");
let f = Foo::new(("Mary", 16)); 
```

#### 使用枚举

请记住，Rust 中的枚举可以包含实际数据，因此我们也可以实现一个函数，该函数将枚举作为参数，该枚举具有每种它接受的值的值。

```
pub enum FooCtorArgs {
   String(String),
   StringU16(String, u16)
}

impl Foo {
  pub fn new(v: FooCtorArgs) {
    match v {
      FooCtorArgs::String(s) => { /* ... */ }
      FooCtorArgs::StringU16(s, i) => { /* ... */ }
    }
  }
}
//...
let f = Foo::new(FooCtorArgs::String("Bob".to_string()));
let f = Foo::new(FooCtorArgs::StringU16("Mary".to_string(), 16)); 
```

# 错误处理

# 错误处理

C++ 允许代码抛出和捕获异常。顾名思义，异常表示异常错误。异常被抛出以中断当前的逻辑流程，并允许堆栈中更高级别的东西捕获异常并恢复情况。如果没有东西捕获抛出，则线程本身将退出。

```
void do_something() {
  if (!read_file()) {
    throw std::runtime_error("read_file didn't work!");
  }
}
...
try {
  do_something();
}
catch (std::exception e) {
   std::cout << "Caught exception -- " << e.what() << std::endl;
} 
```

大多数编码准则会建议仅在真正异常的情况下适度使用异常，并对普通失败使用返回码和其他形式的错误传播。但是 C++ 没有简单的方法来传递普通失败的错误信息，异常可能会变得复杂难以跟踪，并可能引发自身问题。

Rust 不支持异常。Rust 程序应该使用诸如 `Option` 或 `Result` 这样的类型将错误传播给调用者。换句话说，代码应该预期错误并编写处理它们的代码。

`Option` 枚举要么返回 `None`，要么返回 `Some`，其中 `Some` 是一组数据的有效载荷。它是一个泛型枚举，指定了它可能包含的数据类型：

```
enum Option<T> {
   None
   Some(T)
} 
```

例如，我们可能有一个函数，用于搜索数据库中某人的详细信息，它要么找到它们，要么找不到。

```
struct Person { /* ... */}

fn find_person(name: &str) {
   let records = run_query(format!("select * from persons where name = {}", sanitize_name(name)));
   if records.is_empty() {
      None
   }
   else {
      let person = Person::new(records[0]);
      Some(person)
   }
} 
```

`Result` 枚举要么返回某种类型的值，要么返回某种类型的错误。

```
enum Result<T, E> {
  Ok(T),
  Err(E)
} 
```

因此，我们可能有一个函数 `set_thermostat` 用于设置室温。

```
fn set_thermostat(temperature: u16) -> Result<(), String> {
   if temperature < 10 {
     err(format!("Temperature {} is too low", temperature))
   }
   else if temperature > 30 {
     err(format!("Temperature {} is too high", temperature))
   }
   else {
     Ok(())
   }
}
// ...
let result = set_thermostat();
if result.is_ok() {
  // ...
} 
```

此函数将返回一个成功的单位 `()` 值，或者一个失败的 `String`。

## ? 指令

假设你有 2 个函数 `delete_user` 和 `find_user`。函数 `delete_user` 首先调用 `find_user` 来查看用户是否存在，然后继续删除用户或返回从 `find_user` 得到的错误代码。

```
fn delete_user(name: &str) -> Result<(), ErrorCode> {
  let result = find_user(name);
  if let Ok(user) = result {
     // ... delete the user
     Ok(())
  }
  else {
    Err(result.unwrap_err())
  }
}

fn find_user(name: &str) -> Result<User, ErrorCode> {
  //... find the user OR
  Err(ErrorCode::UserDoesNotExist)
} 
```

我们在 `delete_user` 中有很多代码来处理 `find_user` 的成功或失败，并将其失败代码向上抛出。因此，Rust 提供了一个方便的 `?` 标记，放在对函数的调用的末尾，指示编译器生成我们手工编写的 if/else 分支，将函数简化为此形式：

```
fn delete_user(name: &str) -> Result<(), ErrorCode> {
  let user = find_user(name)?;
  // ... delete the user
  Ok(())
} 
```

只要你希望将错误传播到调用栈上，这可以消除代码中大量混乱的条件测试，并使其更加健壮。

Rust 的旧版本使用了专用的 `try!()` 宏来实现相同的目的（不要与 C++ 中的 `try-catch` 混淆），它做的事情与上面的相同。因此，如果你看到这样的代码，它和上面的代码是一样的。

```
fn delete_user(name: &str) -> Result<(), ErrorCode> {
  let user = try!(find_user(name));
  // ... delete the user
  Ok(())
} 
```

## 核心选项 - panic!()

如果代码真的想要执行类似于 C++ 中的 throw / catch 的操作，它可以调用 panic!()。

这不推荐用于处理常规错误，仅用于代码无法处理的不规则错误。

此宏将导致线程中止，如果线程是主程序线程，则整个进程将退出。

可以捕获并且应该捕获 `panic!()`，如果 Rust 是从另一种语言调用的话。捕获未绑定的 panic 的方法是在代码中顶部最高点处使用一个闭包来处理它。

```
use std::panic;

let result = panic::catch_unwind(|| {
    panic!("Bad things");
}); 
```

# Lambda 表达式 / 闭包

# Lambda 表达式 / 闭包

## C++11 中的 Lambda

[lambda 表达式](https://msdn.microsoft.com/en-us/library/dd293608.aspx)，或 lambda 是一个可以在调用的范围内声明并传递的匿名函数。

当你想对一些微不足道的小操作进行排序、过滤、搜索或者其他一些操作时，这特别有用，而不必声明和维护一个单独的函数。

在 C++ 中，lambda 的样子是这样的：

```
float values[10] = { 9, 3, 2.1, 3, 4, -10, 2, 4, 6, 7 };
std::sort(values, values + 10, [](float a, float b) {
  return a < b;
}); 
```

这个 lambda 被传递给一个 std::sort 函数，以便根据某些条件对值数组进行排序。

C++ lambda 可以（但不一定）从封闭作用域中捕获变量，如果它希望的话，它可以在 `[]` 部分指定捕获子句，定义捕获的方式。捕获可以是按值或按引用，并且可以明确列出要捕获的变量，也可以指定通过引用或分配捕获一切。捕获变量的 lambda 实际上变成了一个闭包。

```
auto v1 = 10.;
auto v2 = 2.;
// Capture by value
auto multiply = [v1, v2]() { return v1 * v2; };
// Capture by reference
auto sum = [&v1, &v2]() { return v1 + v2; };
cout << multiply() << endl;
cout << sum() << endl;
v1 = 99; // Now v1 in sum() references 99
cout << multiply() << endl;
cout << sum() << endl; 
```

我们可以从输出中看到，`multiply()` 捕获了 `v1` 和 `v2` 的值的副本，而 `sum()` 捕获的是引用，因此它对变量的变化是敏感的：

```
20
12
20
101 
```

一个捕获还可以通过在捕获子句中指定 `=` 或者引用 `&` 来指定默认捕获模式，然后为特定变量指定捕获行为。

所以我们上面的捕获可以简化为：

```
// Capture by value
auto multiply = [=]() { return v1 * v2; };
// Capture by reference
auto sum = [&]() { return v1 + v2; }; 
```

注意，C++ lambda 可能会表现出危险的行为 - 如果 lambda 捕获了对超出作用域的变量的引用，那么 lambda 的行为是未定义的。在实践中，这可能意味着应用程序崩溃。

## Rust 中的闭包

Rust 实现了闭包。闭包类似于 lambda，除了它自动捕获它从封闭环境中引用的任何东西。也就是说，它默认可以访问任何在封闭作用域中的变量。

这里是我们在 Rust 中看到的相同的排序片段，它表达为 Rust。这个闭包不从其封闭作用域中借用任何东西，但它确实接受一对参数来比较两个值进行排序。`sort_by()` 函数重复调用闭包来对数组进行排序。

```
use std::cmp::Ord;
let mut values = [ 9.0, 3.0, 2.1, 3.0, 4.0, -10.0, 2.0, 4.0, 6.0, 7.0 ];
values.sort_by(|a, b| a < b );
println!("values = {:?}", values); 
```

使用封闭作用域中的变量的闭包默认借用它。这意味着在闭包的作用域内，借用变量是不能改变的。要改变值，我们必须确保闭包超出作用域以释放借用，比如使用一个块：

```
let mut x = 100;
{
  let square = || x * x;
  println!("square = {}", square());
}
x = 200; 
```

或者你可以 `move` 闭包中使用的变量，使其拥有它们，并且它们在外部作用域中不可访问。由于我们的闭包正在访问一个整数，move 变成了隐式复制。所以我们的 `square` 闭包有它自己的 `x`，赋值为 `100`。即使我们将外部作用域中的 `x` 改为 `200`，闭包也有它自己独立的副本。

```
let mut x = 100;
let square = move || x * x;
println!("square = {}", square()); // 10000
x = 200;
println!("square = {}", square()); // 10000 
```

这相当于上面使用 lambda 表达式绑定到副本和引用的 C++ 代码：

```
let mut v1 = 10.0;
let v2 = 2.0;
let multiply = move || v1 * v2;
let sum = |x: &f64, y: &f64| x + y;
println!("multiply {}", multiply());
println!("sum {}", sum(&v1, &v2));
v1 = 99.0;
println!("multiply {}", multiply());
println!("sum {}", sum(&v1, &v2)); 
```

这将产生与 C++ 代码相同的结果。这里的主要区别是，我们没有将闭包绑定到引用，而是将引用值作为参数传递给闭包。

# 模板 / 泛型

# 模板 / 泛型

C++ 提供了模板作为一种编写通用代码的方式，使用抽象类型然后通过将一个或多个类型替换为具体类来特化它。

```
template <typename T>
inline void debug(const T &v) {
  cout << "The value of object is " << v << endl;
}
//...
debug(10); 
```

此模板使用参数的类型（在此示例中为 10）来创建一个内联函数，该函数打印出该类型的值：

```
The value of object is 10 
```

类也可以由模板制作：

```
template <class T>
class Stack {
private:
  vector<T> elements;
public:
  void push(const T &v) {
    // ...
  }
  T pop() {
    // ...
  }
}
//...
Stack<double> doubleStack; 
```

这个类使用模板来指示它包含的对象的类型，实现了一个简单的堆栈。

这是一个非常强大的机制，C++ 库广泛使用它。

模板可能会变得有点混乱，因为模板是内联的，编译器会在尝试编译之前展开你调用的任何东西。

一个看似无害的错误，比如在集合中使用没有默认复制构造函数的类型，可能会导致编译器疯狂输出一堆难以理解的错误。

## 泛型函数

Rust 的模板等效物被称为泛型。泛型将函数或特征泛化，使其适用于符合条件的不同类型。

因此，C++ 中的 `debug()` 函数的 Rust 等效物将是这样的。

```
use std::fmt;

fn debug<T>(data: T) where T: fmt::Display {
  println!("The value of object is {}", data);
}
//...
debug(10); 
```

这里我们描述了一个接受泛型类型 `T` 的函数，其中约束是 `T` 必须实现 `std::fmt::Display` 特征。实现此特征的任何结构都可以传递给调用。由于整数类型实现了该特征，我们可以直接调用它作为 `debug(10)`，编译器会很高兴。

## 泛型结构体

同样，我们可以在结构体上使用泛型。因此，在 Rust 中与 C++ 模板类 `Stack` 的等效物是这样的：

```
struct Stack<T> {
  elements: Vec<T>
}

impl<T> Stack<T> {
  fn new() -> Stack<T> { Stack { elements: Vec::new() } }

  fn push(v: T) {
    //...
  }

  fn pop() -> Option<T> {
    //...
    None
  }
}
//...
let double_stack: Stack<f64> = Stack::new(); 
```

## Where 子句

`where` 子句可以添加以强制施加约束，指定泛型类型必须执行哪些操作才能被提供给泛型函数或结构。

例如，我们可能有一个以闭包作为参数的函数。闭包是一个函数，所以我们想定义闭包将采取的形状。

所以：

```
fn compare<T, F>(a: T, b: T, f: F) -> bool 
  where F: FnOnce(T, T) -> bool 
{
  f(a, b)
}

let comparer = |a, b| a < b;
let result = compare(10, 20, comparer); 
```

这里我们定义了一个 `compare()` 函数，它接受相同类型的一对值。`where` 子句规定函数必须接受两个相同类型的值并返回布尔值。编译器将确保我们传递的任何闭包都符合这个标准，就像我们的 `comparer` 闭包一样。

# 属性

# 属性

C++ 有各种方式在编译期间给出编译器*指令*：

+   控制许多行为的编译标志

+   `#pragma` 语句 - `once`、`optimize`、`comment`、`pack` 等。一些 pragma，如 `comment`，在某些编译器中已被广泛滥用，用于向目标文件中插入“注释”，以控制符号的导入/导出、静态链接和其他功能。

+   使用普遍存在的 `#ifdef` / `#else` / `#endif` 块进行 `#define` 定义

+   关键字 `inline`、`const`、`volatile` 等。这些提示代码并允许编译器做出可能改变其输出或优化的决策。编译器通常有自己的专有扩展。

Rust 使用一种称为 *属性* 的标记，它在更一致的形式中扮演类似的角色。

属性`#[foo]`适用于在其之前声明的下一个项目。常见属性用于用`#[test]`表示单元测试用例：

```
#[test]
fn this_is_a_test() {
  //...
} 
```

属性也可以表示为`#![foo]`，这会影响它们所包含的内容而不是跟随它们的内容。

```
fn this_is_a_test() {
  #![test]
  //...
} 
```

属性被包含在`#[ ]`块中，并提供编译器指令，允许：

+   将函数标记为单元测试或基准测试

+   将函数标记为针对目标操作系统进行条件编译。可以定义仅适用于一个目标的函数。例如，与另一个进程通信的代码在 Windows 和 Linux 上封装在同一个函数中，但实现方式不同。

+   启用/禁用 lint 规则

+   启用/禁用编译器功能。Rust 的某些功能可能是实验性的或已弃用的，可能需要启用才能访问。

+   将入口函数从 `main` 更改为其他内容

+   根据目标体系结构、操作系统、家族、字节顺序、指针宽度进行条件编译

+   内联提示

+   推导出某些特征

+   启用编译器功能，例如实现过程宏的插件。

+   从其他 crate 导入宏

+   被某些 crate（如 serde 和 rocket）用于仪器化代码 - 注意：Rocket 使用不稳定的编译器钩子进行此操作，因此限制自己仅在夜间构建中工作。

## 条件编译

条件编译允许您测试目标配置，并选择性地编译函数或模块。

您将测试的主要配置包括：

+   目标体系结构 - "x86"、"x86_64"、"mips"、"arm"等。

+   目标操作系统 - "windows"、"macos"、"ios"、"linux"、"android"、"freebsd"等。

+   目标家族 - "unix" 或 "windows"

+   目标环境 - "gnu"、"msvc" 等

+   目标字节顺序

+   目标指针宽度

因此，如果您有一个函数在 Windows 上以一种方式实现，在 Linux 上以另一种方式实现，您可以像这样编写它：

```
#[cfg(windows)]
fn get_app_data_dir() -> String { /* ... */ }

#[cfg(not(windows))]
fn get_app_data_dir() -> String { /* ... */ } 
```

更多可能性在[文档](https://doc.rust-lang.org/reference/attributes.html#crate-only-attributes)中列出。

## 链接到本地库

在 C/C++ 中，代码首先编译，然后通过向编译器添加额外参数或调用链接器进行链接。

在 Rust 中，只要使用 `cargo`，大部分的链接工作都是自动完成的。

1.  所有源代码都会被编译和链接在一起。

1.  外部 crate 会自动构建为静态库并链接进来。

1.  但是，如果您必须通过 FFI 链接到外部内容，则必须在您的 `lib.rs` 或 `main.rs` 中编写 `#link` 指令。这在某种程度上类似于 C++ 中的 `#pragma(comment, "somelib")`。

| C++ | Rust |
| --- | --- |
| `#pragma (comment, "somelib")` | `#[link(name = "somelib")]` |
| - | `#[link(name = "somelib", kind = "static")]` |

`#link`的默认类型是`dynamic`库，但可以明确指定为`static`。

## 内联代码

内联发生在您的函数逻辑被插入到调用它的代码中的地方。当函数执行一些微不足道的操作，比如返回一个值或执行一个简单的条件时，它往往会发生。复制代码的开销被性能好处所抵消。

在 C++ 中，可以通过在头文件中声明和实现函数、类方法或模板方法或者使用 inline 关键字标记来实现内联。

在 Rust 中，内联只是一个提示。Rust 建议不要强制内联，而是将其留作 LLVM 编译器根据需要处理的提示。

| C++ | Rust |
| --- | --- |
| 显式使用 `inline` 或隐式通过在类/结构中实现的方法 | `#[inline]`、`#[inline(always)]`、`#[inline(never)]` |

显式内联代码的另一种选择是使用 LLVM 中的链接时优化。

```
rustc -C lto 
```

# 多线程

# 多线程

多线程允许你同时运行编程的部分，以并行方式执行任务。每个程序都有一个*主*线程 - 即你的`main()`从中启动的线程，另外还有您创建的任何线程。

使用线程的原因示例：

+   长时间运行的操作，例如压缩一个大文件。

+   阻塞式的活动，例如在套接字上监听连接

+   并行处理数据，例如物理、碰撞检测等。

+   异步活动，例如定时器、轮询操作。

此外，如果使用图形工具包或第三方库，它们可能会生成您不知道的线程。

## 线程安全

在多线程中，您会经常听到一个词叫线程安全。

具体来说：

+   线程不应能够同时修改数据。当这种情况发生时，称为数据竞争，可能会损坏数据，导致崩溃。例如，两个线程同时尝试追加到一个字符串。

+   线程不应以可能导致死锁的方式锁定资源，即线程 1 获得资源 B 的锁并在资源 A 上阻塞，而线程 2 获得资源 A 的锁并在资源 B 上阻塞。两个线程将永远被锁定，等待永远不会释放的资源。

+   竞争条件是不好的，即线程执行顺序对相同输入的输出产生不可预测的结果。

+   可以被多个线程调用的 API 必须要么保护它们的数据结构，要么明确地让客户端解决这个问题。

+   被多个线程访问的打开文件和其他资源必须安全地进行管理。

### 保护共享数据

数据不应在另一个线程同时读取和写入。也不应该由两个线程同时写入数据。

防止这种情况的常见方式是：

+   使用互斥锁来保护数据访问。互斥锁是一种特殊的类，一次只能有一个线程锁定。尝试锁定互斥锁的其他线程将等待，直到另一个线程持有的锁被释放。

+   使用读写锁。类似于互斥锁，它允许一个线程锁定用于写入数据的线程，但允许多个线程具有读取访问权限，前提是没有其他线程正在写入数据。对于频繁读取而不是修改的数据，这比仅使用互斥锁要高效得多。

### 避免死锁

避免死锁的最佳方法是只锁定一件事情，并在完成后立即释放。但如果必须锁定多个事物，请确保所有线程之间的锁定顺序是一致的。因此，如果线程 1 锁定 A 和 B，则确保线程 2 也按照这个顺序锁定 A 和 B，而不是 B 然后 A。后者肯定会导致死锁。

## C / C++

C 和 C++ 在某种程度上早于线程，因此直到 C++11 之前，这两种语言对多线程几乎没有内置支持，而且存在的支持往往是特定于编译器的扩展。

这导致 C 和 C++ 没有线程安全的强制执行。如果数据竞争 - 很遗憾。如果你忘记在一个函数中写锁，即使你记住了所有其他函数 - 很遗憾。你必须自律地考虑并在必要时应用适当的保护。

不这样做的后果可能甚至在您的软件投入生产并且某个客户开始抱怨他们的服务器每周冻结一次时才会感受到。祝你好运找到那个 bug！

### 多线程 API

最常见的 API 包括：

+   `<thread>`, `<mutex>` - 从 C++11 开始

+   POSIX 线程，或者 pthreads。由类似 Linux 和大多数其他 Unix 派生系统（例如 OS X）的 POSIX 系统提供支持。还有在 Win32 线程之上构建的 pthread-win32 支持。

+   Win32 线程。由 Windows 操作系统提供支持。

+   OpenMP。许多 C++ 编译器支持。

+   第三方库如 Boost 和 Qt 提供了封装，抽象了线程 API 之间的差异。

所有 API 都有共同点：

+   线程的创建、销毁、加入（等待线程）和分离（释放线程以自由执行其操作）。

+   使用锁和屏障在线程之间进行同步。

+   互斥锁 - 保护共享数据的互斥锁。

+   条件变量 - 一种信号和通知条件变为真的方法。

### std::thread

`std::thread` 代表一个执行线程，并提供了一个在各种平台上处理线程的抽象方式。

```
#include <iostream>
#include <thread>

using namespace std;

void DoWork(int loop_count) {
    for (int i = 0; i < loop_count; ++i) {
        cout << "Hello world " << i << endl;
    }
}

int main() {
    thread worker(DoWork, 100);
    worker.join();
} 
```

该示例生成一个线程，调用该函数并将参数传递给它，打印一条消息 100 次。

### std::mutex

C++ 提供了一系列不同的 `mutex` 类型来保护对共享数据的访问。

互斥锁由 `lock_guard` 获取，并且其他尝试获取互斥锁的尝试将被阻塞，直到锁被释放。

```
#include <iostream>
#include <thread>
#include <mutex>

using namespace std;

mutex data_guard;
int result = 0;

void DoWork(int loop_count) {
    for (auto i = 0; i < loop_count; ++i) {
        lock_guard<mutex> guard(data_guard);
        result += 1;
    }
}

int main() {
    thread worker1(DoWork, 100);
    thread worker2(DoWork, 150);
    worker1.join();
    worker2.join();
    cout << "result = " << result << endl;
} 
```

### POSIX 线程

pthreads API 以`pthread_`为前缀，并且工作原理如下：

```
#include <iostream>
#include <pthread.h>

using namespace std;

void *DoWork(void *data) {
    const int loop_count = (int) data;
    for (int i = 0; i < loop_count; ++i) {
        cout << "Hello world " << i << endl;
    }
    pthread_exit(NULL);
}

int main() {
    pthread_t worker_thread;
    int result = pthread_create(&worker_thread, NULL, DoWork, (void *) 100);
    // Wait for the thread to end
    result = pthread_join(worker_thread, NULL);
} 
```

这个示例生成一个线程，调用带有 100 载荷的 DoWork，导致函数打印消息 100 次。

### Win32 线程

Win32 线程具有类似于 POSIX 的函数。它们的名称如`CreateThread`、`ExitThread`、`SetThreadPriority`等。

### OpenMP API

Open Multi-Processing（OpenMP）是用于多线程并行处理的 API。OpenMP 依赖于编译器支持，因为你在源代码中使用特殊的`#pragma`指令来控制线程创建和对数据的访问。

GCC、Clang 和 Visual C++ 都支持 OpenMP，所以这是一个选择。

OpenMP 是一个复杂的标准，但使用指令可以使代码比直接调用线程 API 更清晰。缺点是它也更加不透明，隐藏了软件正在做的事情，使得调试变得相当困难。

OpenMP 在 OpenMP [网站](http://www.openmp.org/)上有详细描述。

### 线程局部存储

线程局部存储，或 TLS 是静态或全局数据，对于每个线程都是私有的。每个线程都持有自己的数据副本，因此可以修改它而不必担心造成数据竞争。

编译器还有专有的方法来将类型标记为线程本地：

```
__thread int private; // gcc / clang
__declspec(thread) int private; // MSVC 
```

C++11 引入了`thread_local`指令，用于修饰应使用 TLS 的变量。

```
thread_local int private 
```

## Rust

我们在 C++ 中看到，你必须严格遵守保护数据免受竞态条件的规定。

Rust 不会给你那样的奢侈 -

1.  你共享的任何数据都必须以线程安全的方式保护。

1.  你在线程之间传递的任何数据都必须标记为线程安全。

### 创建一个线程

通过调用`spawn`并提供你想在新线程中运行的闭包，轻松创建一个线程。

```
use std::thread;

thread::spawn(move || {
  println!("Hello");
}); 
```

或者你可以提供一个函数给`spawn`，以相同的方式调用它。

```
fn my_thread() {
  println!("Hello");
}
//...
thread::spawn(my_thread); 
```

如果提供一个闭包，则必须具有`'static`的生命周期，因为线程可能会超出创建它的范围。即它们默认是分离的。

闭包可以使用标记为`Send`的移动值，因此编译器允许所有权在线程之间转移。

同样函数/闭包也可以返回一个标记为`Send`的值，因此编译器可以在终止线程和调用`join`以获取值的线程之间转移所有权。

所以上面的线程是分离的。如果我们想等待线程完成，`spawn`返回一个`JoinHandle`，我们可以调用`join`等待终止。

```
let h = thread::spawn(move || {
  println!("Hello");
});
h.join(); 
```

如果闭包或函数返回一个值，我们可以使用`join`来获取它。

```
let h = thread::spawn(move || 100 * 100);
let result = h.join().unwrap();
println!("Result = {}", result); 
```

### 编译器中的数据竞争保护

数据竞争是坏消息，但幸运的是在 Rust 中编译器会支持你。你必须保护你的共享数据，否则它不会编译通过。

保护你的数据最简单的方法是将数据包装在互斥锁中，并为每个线程实例提供一个引用计数的锁的副本。

```
let shared_data = Arc::new(Mutex::new(MySharedData::new()));

// Each thread we spawn should have a clone of this Arc
let shared_data = shared_data.clone();
thread::spawn(move || {
  let mut shared_data = shared_data.lock().unwrap();
  shared_data.counter += 1;
}); 
```

这里是一个完整的示例，生成 10 个线程，每个线程都增加计数器。

```
struct MySharedData {
  pub counter: u32,
}

impl MySharedData {
  pub fn new() -> MySharedData {
    MySharedData {
      counter: 0
    }
  }
}

fn main() {
  spawn_threads();
}

fn spawn_threads() {
  let shared_data = Arc::new(Mutex::new(MySharedData::new()));

  // Spawn a number of threads and collect their join handles
  let handles: Vec<JoinHandle<_>> = (0..10).map(|_| {
    let shared_data = shared_data.clone();
    thread::spawn(move || {
      let mut shared_data = shared_data.lock().unwrap();
      shared_data.counter += 1;
    })
  }).collect();

  // Wait for each thread to complete
  for h in handles {
    h.join();
  }

  // Print the data
  let shared_data = shared_data.lock().unwrap();
  println!("Total = {}", shared_data.counter);
} 
```

所以基本策略将是这样的：

1.  每个线程将获得自己的互斥锁的原子引用。

1.  每个希望访问共享数据的线程都必须在互斥锁上获取锁。

1.  一旦锁被释放，下一个等待的线程就可以获得访问权限。

1.  如果有任何问题，编译器将强制执行并生成错误。

### 读写锁

读写锁的工作方式与互斥锁类似-我们将共享数据包装在`RwLock`中，然后在`Arc`中包装。

```
let shared_data = Arc::new(RwLock::new(MySharedData::new())); 
```

然后每个线程都需要在共享数据上获取读锁或写锁。

```
let shared_data = shared_data.read().unwrap();
// OR
let mut shared_data = shared_data.write().unwrap(); 
```

`RwLock`的优势在于许多线程可以同时读取数据，只要没有线程在写入数据。在许多情况下，这可能更有效率。

### 使用通道在线程之间发送数据

TODO mpsc 通道

### 线程本地存储

与 C++一样，您可能有理由使用线程本地存储

```
thread_local! {
  // TODO
} 
```

### 有用的 crate

#### Rayon

[rayon](https://github.com/rayon-rs/rayon) crate 实现了并行迭代器，允许您的集合并行迭代。该 crate 利用工作窃取和分治算法与线程池结合，以比顺序方式更快地处理集合。

一般来说，这是一个可替换的方案，唯一的例外是您调用`par_iter`而不是`iter`。该 crate 在集合类上实现了`ParallelIterator` trait。

```
use rayon::prelude::*;
fn sum_of_squares(input: &[i32]) -> i32 {
    input.par_iter()
         .map(|&i| i * i)
         .sum()
} 
```

查看 crate 网站获取更多信息。

# 代码检查

# 代码检查

C/C++编译器可以发出许多有用的警告，但它们可以进行的静态分析通常相当有限。

Rust 编译器对数据执行更严格的生命周期检查，然后进行代码检查，检查您的代码是否存在潜在的错误或错误

特别是它寻找：

+   无效/未使用的代码

+   不可达代码

+   废弃的方法

+   未记录的函数

+   驼峰命名法/蛇形命名法违规

+   无限递归代码（即没有条件停止递归）

+   在可以使用堆栈的情况下使用堆内存

+   未使用的外部 crate、导入、变量、属性、mut、括号

+   使用"while true {}"而不是"loop {}"

通过使用属性可以更严格地执行或忽略代码检查规则：

```
#[allow(rule)]
#[warn(rule)]
#[deny(rule)]
#[forbid(rule)] 
```

可以��过键入"rustc -W help"找到 lint 规则的完整列表：

```
 name  default  meaning
                         ----  -------  -------
                box-pointers   allow    use of owned (Box type) heap memory
           fat-ptr-transmutes  allow    detects transmutes of fat pointers
 missing-copy-implementations  allow    detects potentially-forgotten implementations of `Copy`
missing-debug-implementations  allow    detects missing implementations of fmt::Debug
                 missing-docs  allow    detects missing documentation for public members
                trivial-casts  allow    detects trivial casts which could be removed
        trivial-numeric-casts  allow    detects trivial casts of numeric types which could be removed
                  unsafe-code  allow    usage of `unsafe` code
... 
```

这里列出了许多检查。

# 宏

# 宏

## C/C++预处理器

C 语言在编译时有点不同寻常。第一阶段称为预处理。在此阶段，预处理器查找以#符号开头的指令，并根据这些指令进行字符串替换和条件包含/排除。只有在文件经过预处理后，编译器才尝试编译它。

预处理指令以`#`符号开头。例如，`#define`指令创建一个带有可选值的宏：

```
#define IS_WINDOWS
#define SHAREWARE_VERSION 1 
```

我们将在稍后更深入地探讨宏。另一个指令是`#if\#else\#endif`或`#ifdef\#else\#endif`，根据匹配情况从测试的一个分支或另一个分支包含代码。

```
#if SHAREWARE_VERSION == 1
showNagwarePopup();
#endif
//...
#ifdef IS_WINDOWS
writePrefsToRegistry();
#else
writePrefsToCfg();
#endif 
```

另一个指令是 `#include`。在 C 和 C++ 中，公共函数和结构通常在不同的文件中定义和实现。`#include` 指令允许将头文件拉入到使用这些定义的任何文件的前面。

```
// System / external headers tend to use angle style
#include <string>
#include <stdio.h>

// Local headers tend to use double quotes
#include "MyClass.h" 
```

在所有这些情况下需要记住的重要事情是，这些事情都发生在编译器甚至开始之前！你的 `main.c` 可能只有 10 行代码，但如果你 `#include` 了一些头文件，预处理器可能会将成千上万行的类型、函数馈送到编译器中，在它们到达你的代码之前都会被评估。

## C / C++ 宏

宏是在源代码编译之前由预处理器执行的字符串替换模式。因此，它们很容易出错，因此已被废弃，而常量和内联函数更受青睐。

这是一个简单的宏，行为可能出乎意料：

```
#define MULTIPLY(x, y) x * y
//
int x = 10, y = 20;
int result = MULTIPLY(x + 1, x + y);
// Value is NOT 330 (11 * 30), it's 41 because macro becomes x + 1 * x + y 
```

这个宏非常简单 - 将 x 乘以 y。但如果任一参数是表达式，则会失败。在这种情况下，合理使用括号可能会避免错误，但我们仍然可以通过一些预增量或后增量再次打破它。

C++ 中的宏也是不卫生的，即宏可能会无意间与或捕获到外部值发生冲突，导致代码错误。

```
#define SWAP(x, y) int tmp = y; y = x; x = y;
//
int tmp = 10;
int a = 20, b = 30;
SWAP(a, b); // ERROR 
```

这里我们的 SWAP 宏使用了一个名为 `tmp` 的临时值，这个值已经存在于作用域中，所以编译器会报错。宏可以通过使用在 `do / while(0)` 块内的影子变量来避免冲突，但这并不理想。

```
#define SWAP(x, y) do { int tmp = y; y = x; x = y } while(0); 
```

因此，尽可能使用内联函数。即便如此，宏在这些角色中仍然经常被使用：

+   用于根据命令行标志或指令进行条件包含，例如编译器可能会 `#define WIN32`，以便根据其是否存在来有条件地进行编译。

+   用于在头部周围添加守卫块，以防止它们被 #include 多次。大多数编译器实现了一个“#pragma once 指令”，这是一个越来越常见的替代方案。

+   用于生成一些样板代码片段（例如命名空间包装器）或者根据 #define（例如是否设置了 DEBUG）等情况可能会被编译删除的东西。

+   用于生成值字符串和其他奇特边缘情况

编写宏很容易，也许太容易了：

```
#define PRINT(x) \
  printf("You printed %d", x); 
```

这个宏在编译前会展开为 printf，但如果 x 不是整数，则编译失败或打印错误的内容。

## Rust 宏

Rust 中的宏是一个相当复杂的话题，但它们比 C++ 中的更强大、更安全。

+   Rust 的宏是卫生的。也就是说，如果一个宏包含变量，它们的名称不会与所在作用域中的命名变量发生冲突、隐藏或以其他方式干扰。

+   在宏的方括号之间提供的模式被标记为 Rust 语言的一部分并进行标记化。标识符，表达式等。在 C / C++ 中，你可以将一个宏 #define 为任何你喜欢的东西，无论它是垃圾还是符合语法规范。此外，你可以从任何地方调用它，因为它在编译器看到代码之前就被预处理了。

+   Rust 宏要么是声明性的和基于规则的，每个规则都有一个左手边模式 "匹配器" 和一个右手边 "替换"。要么它们是过程性的，实际的 rust 代码将一个输入转换成一个输出（见下面的部分）。

+   宏必须生成符合语法规范的代码。

+   声明性宏可以由 crate 导出，并在其他代码中使用，前提是其他代码选择启用 crate 的宏支持。这有点混乱，因为它必须用 #[macro_export] 指令来标志。

说了这么多，Rust 中的宏 *确实* 很复杂 - 也许太复杂了 - 一般来说应该尽可能地少用。

这是一个简单的声明性宏，演示了重复称为 hello_x!()。它将接受逗号分隔的表达式列表，并对其中的每个表达式都说 hello。

```
macro_rules! hello_x {
  ($($name:expr),*) => (
    $(println!("Hello {}", $name);)*
  )
}
// The code can supply as many arguments it likes to this macro
hello_x!("Bob", "Sue", "John", "Ellen"); 
```

本质上，匹配器针对我们的逗号分隔列表进行匹配，替换生成一个包含每个表达式消息的 println!()。

```
Hello Bob
Hello Sue
Hello John
Hello Ellen 
```

如果我们在数组中加入一些其他表达式会怎样呢？

```
hello_x!("Bob", true, 1234.333, -1); 
```

好吧，这也可以：

```
Hello Bob
Hello true
Hello 1234.333
Hello -1 
```

有些非法代码怎么样：

```
hello_x!(Aardvark {}); 
```

我们从宏中得到一个有意义的错误。

```
error[E0422]: `Aardvark` does not name a structure
  |
8 | hello_x!(Aardvark {});
  |          ^^^^^^^^
<std macros>:2:27: 2:58 note: in this expansion of format_args!
<std macros>:3:1: 3:54 note: in this expansion of print! (defined in <std macros>)
<anon>:5:7: 5:35 note: in this expansion of println! (defined in <std macros>)
<anon>:8:1: 8:23 note: in this expansion of hello_x! (defined in <anon>) 
```

## 真实世界的例子 - vec!()

Rust 自带了很多宏，用于减少一些繁琐模板的工作。例如，vec!() 宏是声明一个 std::Vec 并预先填充一些值的方法。

这是从 Rust 源代码中提取的 vec! 宏的实际源代码：

```
macro_rules! vec {
    ($elem:expr; $n:expr) => (
        $crate::vec::from_elem($elem, $n)
    );
    ($($x:expr),*) => (
        <[_]>::into_vec(box [$($x),*])
    );
    ($($x:expr,)*) => (vec![$($x),*])
} 
```

看起来很复杂，但我们将拆解它以了解它的作用。首先，它具有与 match 相似的语法，有三个展开到与左手边匹配的任何内容的分支：

### 第一个分支

第一个匹配器匹配一个模式，比如 `1; 100`。值 `1` 进入 `$elem`，值 `100` 进入 `$n`：

```
($elem:expr; $n:expr) =>  (
        $crate::vec::from_elem($elem, $n)
    ); 
```

`$crate` 是一个特殊值，解析为模块 crate，恰好是 std。

所以这就扩展成了这样：

```
let v = vec!(1; 100);
// 1st branch matches and it becomes this
let v = std::vec::from_elem(1, 100); 
```

### 第二个分支

第二个匹配器包含一个全局表达式 - 用逗号分隔的零个或多个表达式（最后一个逗号是可选的）。每个匹配的表达式都会进入 `$x`：

```
($($x:expr),*) => (
        <[_]>::into_vec(box [$($x),*])
    ); 
```

所以我们可以写：

```
let v = vec!(1, 2, 3, 4, 5);
// 3nd branch matches and it becomes this
let v = <[_]>::into_vec(box [1, 2, 3, 4, 5]); 
```

box 关键字告诉 Rust 在堆上分配提供的数组，并通过调用一个名为 into*vec() 的辅助函数转移所有权，该函数使用一个 Vec 实例包装内存数组。前面的 <[\*]>:: 是一种 turbo-fish 符号，让 into_vec() 泛型函数快乐地工作。

### 第三个分支

第三个分支有点奇怪，几乎和第二个分支看起来一样。但是看看逗号。在上一个分支中，逗号在星号旁边，这次它在内部 $() 中。

```
($($x:expr,)*) => (vec![$($x),*]) 
```

当逗号存在时，匹配器匹配，如果是这样，则递归调用 vec!() 再次解析到第二个分支匹配器：

基本上，这样做是为了我们的声明中可以有一个尾随逗号，而它仍然会生成相同的代码。

```
// 3rd branch matches this
let v = vec!(1, 2, 3, 4, 5,);
// and it becomes this
let v = vec!(1, 2, 3, 4, 5);
// which matches 2nd branch to become
let v = <[_]>::into_vec(box [1, 2, 3, 4, 5]); 
```

## 过程宏

到目前为止，我们已经讨论了展开为 Rust 代码的声明性宏，这是基于宏定义的规则进行模式匹配的。

第二种宏是*过程宏*。过程宏是用 Rust 编写的插件，由编译器编译和加载，以生成任意的 Rust 代码���为其输出。

因此，过程宏可以被视为一个代码生成器，但它是实际编译器的一部分。过程宏特别适用于：

+   序列化 / 反序列化（例如，[serde](https://github.com/serde-rs/serde) 模块生成用于将结构体读写到各种格式 - JSON、YAML、TOML、XML 等的代码。）

+   领域特定语言（例如嵌入式 SQL，正则表达式等）。

+   面向方面的编程（例如额外的调试、性能指标等）

+   新的 lint 和 derive 规则

欲了解更多信息，请查看 Rust 书中关于[编译器插件](https://doc.rust-lang.org/book/compiler-plugins.html)的部分。

## 其他形式的条件编译

我们看到 C / C++ 预处理器可用于条件编译。在 Rust 中的等价物是属性。查看属性部分以了解它们的用法。

# 内存分配

# 内存分配

本节涉及内存分配，即在堆上创建对象而不是在栈上创建对象，以及它们的创建和销毁方式。

## C++

C 和 C++ 有各种标准的内存分配方式：

1.  `malloc`/`calloc`/`realloc()` 和 `free()` 函数

1.  `new` 和 `delete`（仅限 C++）

1.  `new[]` 和 `delete[]` 用于数组（仅限 C++）

在 C++ 类或结构体上调用 `malloc()`/`free()` 绝不是一个好主意，因为它不会调用相应的类构造函数或析构函数。`realloc()` 函数分配一个新的内存块，在释放原始内存之前复制现有内存块的内容。

```
// malloc / free
char *buffer = (char *) malloc(1024);
...
free(buffer);
// new / delete
Stack *stack = new Stack();
...
delete stack;
// new[] / delete[]
Node *nodes = new Node[100];
...
delete []nodes; 
```

在每种情况下，分配必须与相应的释放操作匹配，因此我们立即可以看到这里存在错误的可能性：

1.  所有权规则可能会变得混乱，特别是当一个类被频繁传递时 - 谁删除对象以及何时删除？

1.  不使用正确的 `new` 和 `delete` 对，导致内存泄漏。例如，调用 `delete` 而不是 `delete[]`

1.  忘记释放内存导致内存泄漏。

1.  多次释放内存。

1.  调用悬空指针，即指向已释放内存的指针。

1.  分配 / 释放方式导致堆碎片化。重新分配可能会导致碎片化发生得更快。

C++ 有智能指针，可以管理对象的生命周期，是一种避免程序员错误的好方法：

```
{
  std::auto_ptr<Database> db(new Database());
  //... object is deleted when db goes out of scope
}

// C++11
{
  std::unique_ptr<Database> db(new Database());
  //... object is deleted when db goes out of scope

  std::unique_ptr<Node[]> nodes<new Node[100]);
  //... arrays of objects are supported too
}

// C++11
{
  std::shared_ptr<Database> db(new Database());
  // Reference count db
  setDatabase(db);
  //... object is deleted when last shared_ptr reference to it goes out of scope

  std::shared_ptr<Node[]> nodes<new Node[100]);
  //... arrays of objects are supported too
} 
```

不幸的是，智能指针并非总是可用，但在任何可能的地方都应该使用它们。

### 分配内存的其他方式

几乎每个 C 和 C++库都有管理内存的解决方案。它们都有自己独特的所有权概念，通常各不相同。Boost 和 Qt 有它们自己的内存管理“智能”指针。Qt 甚至要求某些对象由创建对象的线程上的消息处理循环“稍后”删除。一些库甚至采用类似 COM 的引用计数对象与智能指针的模型。大多数 C 库将公开一个 alloc 和 free 函数，用于创建和销毁调用者传递给 API 的上下文对象。

在某些情况下，内存分配甚至可以被覆盖和替换。在 C 中，标准的 malloc / free 可以被替换为另一个内存分配器，例如 TCMalloc [TCMalloc](http://goog-perftools.sourceforge.net/doc/tcmalloc.html)。或者代码可能希望使用垃圾收集内存，在这种情况下[Bohem GC](http://www.hboehm.info/gc/)是一个常用的库。Boehm 还可以用于泄漏检测，因为它可以找到从未释放的对象。C++还可以[覆盖](http://en.cppreference.com/w/cpp/memory/new/operator_new)全局或类特定的 new / delete 运算符。一些标准 C++模板类也允许覆盖内存分配。

## Rust

正如你现在可能猜到的，Rust 在分配方面比 C/C++要严格得多。对象的生命周期由编译器跟踪和强制执行，其中包括内存分配的对象。

在正常的安全编程中，没有显式的 new / delete，因此没有忘记释放对象的方法。也没有指针，因此代码不能调用悬空指针或无意中���用空指针。

1.  一个`Box`是一个持有堆分配对象的托管指针。Box 不能被克隆，因此任何时候只有一个所有者。

1.  一个`Cell`是一个可变的内存位置 - 它可以保存任何可复制的类型，并且其中的值可以被更改。

1.  一个`RefCell`是一个可变的内存位置，可以保存一个引用。

对于程序员来说，一旦正确定义了对象的生命周期，它就会正确地存在和消失。在许多情况下，这种生命周期管理几乎没有运行时成本，或者如果有成本，那也不会超过正确编写的相同代码在 C/C++中的成本。

Rust 要求大多数堆分配的内存由下面的一个或多个结构体包含。结构体管理对象内部的生命周期和访问，确保生命周期被正确管理。

### Box

一个`Box`在堆上进行内存管理。

```
struct Blob {
  data: Box<[u8; 16384]>
}

impl Blob {
  pub fn new() {
    Efficient {
      data: Box::new([0u8; 16384])
    }
  }
} 
```

拥有 Box 的人可以访问它。基本上，这意味着你可以把 Box 从一个地方传递到另一个地方，最后绑定到它的任何东西都可以打开它。其他所有人的绑定将变得无效，并将生成编译错误。

Box 可以用于抽象，因为它可以通过实现的 trait 引用一个结构体，允许类型之间解耦。

TODO 示例，一个结构体持有一个通过另一个结构体实现的 trait 的 Box

它可以用于一段代码代表另一段代码创建对象并移交的情况。Box 始终确保所有权是显式的，当 Box 移动到新所有者时，对象本身的生命周期也会移动。

### Cell

一个`Cell`是可以通过`get()`或`set()`进行复制以覆盖自身副本的东西。由于内容必须是可复制的，它们必须实现 Copy trait。

`Cell`在运行时没有额外开销，因为它不必跟踪借用，但限制是它只适用于 Copy 类型。因此，它不适用于大对象或深拷贝对象。

### RefCell

稍微更有用的是`RefCell<T>`，但它会产生运行时开销以维护读写锁。

`RefCell`持有一个对象的引用，可以被可变借用或不可变借用。这些引用是读写锁定的，因此这会带来运行时开销，因为借用必须检查是否有其他东西已经借用了引用。

通常一段代码可能会在作用域内借用引用，当作用域结束时，借用会消失。如果一个借用发生在最后一个借用释放之前，它会导致恐慌。

## 引用计数对象

Rust 实现了`Rc<>`和`Arc<>`用于引用计数需要被代码不同部分共享和使用的对象。Rc<>是单线程引用计数包装器，而`Arc<>`是原子引用计数包装器。你根据线程是否共享对象来使用其中之一。

一个引用计数对象通常包装着一个`Box`、`Cell`或`Refcell`。因此，多个结构体可以持有对同一对象的引用。

### Rc

来自`std::rc::Rc`。一个引用计数对象可以同时被多个所有者持有。每个所有者持有一个克隆的`Rc<T>`，但 T 内容是共享的。对对象的最后一个引用会导致内容被销毁。

### Arc

来自`std::sync::Arc`。一个原子引用计数对象，工作方式类似于`Rc<T>`，只是它使用原子递增的计数器，使其线程安全。维护原子引用计数需要更多开销。如果多个线程访问同一对象，它们被迫使用`Arc<T>`

# 外部函数接口

# 外部函数接口

Rust 并不是独立存在的，也从未打算如此。相反，它总是假定需要调用其他代码，其他代码也需要调用它，

+   通过它们的入口点调用其他库

+   在 Rust 中生成可以被另一种语言编写的代码调用的库。例如 C、C++、Python、Ruby 等。

为此，它具有外部函数接口，可以定义外部函数、暴露自己的函数而不进行名称混淆，并调用否则在 Rust 中将是非法的不安全代码。

## 调用 C 库

Rust 支持外部函数接口的概念，这是在链接时解析的外部函数或类型的定义。

例如，我们可能希望链接到一个名为 foo.lib 的库，并调用一个命令 foo_command()。

```
#[link(name = "foo")]
extern {
  fn foo_command(command: *mut u8)
} 
```

要调用这个函数，我们必须首先关闭安全检查，因为我们要违反 Rust 生命周期执行的界限。为此，我们将调用包装在一个不安全的块中，以禁用安全检查：

```
pub fn run_command(command: &[u8]) {
  unsafe {
    foo_command(command.as_ptr());
  }
} 
```

注意我们如何在这个不安全块中使用不安全特性，这允许与外界进行交互，同时仍然对我们代码的其余部分进行安全性强制执行。

## 使 Rust 代码可调用

反之亦然，我们可以从 Rust 生成一个库，可以被其他代码调用。

例如，想象一下我们有一些用 Python 编写的代码。代码运行良好，但性能不佳，而且代码的瓶颈只在其中的某一部分，比如某些文件操作，如校验和。我们希望我们的代码由一个 make_checksum() 和一个 release_checksum() 组成。

```
extern crate libc;

use std::ffi::CString;
use std::ptr;
use libc::{c_char, c_void, malloc, memset, strcpy, free};

#[no_mangle]
pub extern "C" fn make_checksum(filepath: *const c_char) -> *mut c_char {
    // Your code here
    if filepath == ptr::null() {
      return ptr::null_mut::<c_char>()
    }

    unsafe {
        // Imagine our checksum code here...
        let result = malloc(12);
        memset(result, 0, 12);
        strcpy(result as *mut c_char, CString::new("abcdef").unwrap().as_ptr());
        return result as *mut c_char;
    }
}

#[no_mangle]
pub extern "C" fn release_checksum(checksum: *const c_char) {
    unsafe {
        free(checksum as *mut c_void);
    }
} 
```

现在在 Python 中我们可以简单地调用该库：

```
import ctypes

checksum = ctypes.CDLL("path/to/our/dll");
cs = checksum.make_checksum("c:/somefile");
...
checksum.release_checksum(cs) 
```

[FFI 规范](https://doc.rust-lang.org/book/ffi.html) 比这更详细，并解释了诸如回调、结构体打包、stdcall、链接等问题，从而实现了完全的互操作性。

## libc

Rust 维护着一个叫做 [libc](https://github.com/rust-lang/libc) 的 crate，其中包含与 C 对应的类型和函数。

依赖于 libc 的 `Cargo.toml` 将被添加到您的项目中：

```
[dependencies]
libc = "0.2.17" 
```

使用这些函数的文件会包含如下的引言，说明调用了哪些类型和函数：

```
extern crate libc;

use libc::{c_char, malloc, free, atoi}; 
```

## 其他库

还有一些包含结构、类型和函数定义的 crates。

+   [WinAPI](https://github.com/retep998/winapi-rs) 对 Win32 编程 API 的绑定

+   [OpenSSL](https://github.com/sfackler/rust-openssl) 对 OpenSSL 的绑定
