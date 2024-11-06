# Rust Cookbook

# Rust Cookbook

## 数字

### 将数字转换为字符串

假设你有一个整数，想要将其转换为字符串。

在 C++中，你可能会执行以下操作之一：

```
const int value = 17;
std::string value_as_string;

// Nonstandard C itoa() (also not thread safe)
value_as_string = itoa(value);

// OR _itoa()
char buffer[16];
_itoa(value, buffer, 10);

// OR
sprintf(buffer, "%d", value);

// OR
stringstream ss;
ss << value;
value_as_string = ss.str();

// OR (boost)
value_as_string = boost::lexical_cast<std::string>(ivalue); 
```

所有这些都有问题。有些是标准的扩展，其他的可能不是线程安全的，有些可能在将 value 更改为另一种类型（例如 long long）时出现问题。

Rust 使得这个过程变得更加容易，因为数值基元实现了一个名为 ToString 的特质。ToString 特质有一个 to_string()函数。所以将数字转换为字符串就像这样简单：

```
let value = 17u32;
let value_as_string = value.to_string(); 
```

浮点数也是如此：

```
let value = 100.00345f32;
let value_as_string = value.to_string(); 
```

### 将数字转换为带精度/填充的字符串

在 C 中，你会使用 printf 操作添加精度或填充：

```
double value = 1234.66667;
char result[32];
sprintf(result, "%08.2d", value); 
```

在 C++中，你可以使用 C 的方式（老实说，这比下面写的更容易），或者你可以通过 ostream 设置填充和精度：

```
// TODO validate
double value = 1234.66667;
ostringstream ss;
ss << setfill('0') << setw(8) << setprecision(2) << value; 
```

在 Rust 中，你可以使用 format!() [[`doc.rust-lang.org/std/fmt/`](https://doc.rust-lang.org/std/fmt/)] 来实现这个目的，它类似于 printf / sprintf：

```
let value = 1234.66667;
let value_as_string = format!("{:08.2}", value);
println!("value = {}", value_as_string); 
```

输出

```
value = 01234.67 
```

### 将数字转换为本地化字符串

一些语言环境会使用点号或逗号作为分隔符。一些语言将使用点号或逗号作为小数点。为了格式化这些字符串，我们需要利用语言环境。

待办事项

### 将字符串转换为数字

在 C / C++中，可以以多种方式将数字从字符串转换为数字

```
 int value = atoi(value_as_str); 
```

待办事项

在 Rust 中，我们有一个包含数字的&str：

```
let value_as_str = "12345"; 
```

任何实现了名为 FromStr 的特质的类型都可以从字符串中获取其类型。所有标准的基本类型都实现了 FromStr，所以我们可以简单地这样说：

```
let value_as_str = "12345";
let value = i32::from_str(value_as_str).unwrap(); 
```

注意末尾的 unwrap() - FromStr::from_str()返回 Result<valueu0002c error="" class="hljs-meta">中的值，以允许字符串无法解析的可能性。生产代码应该在调用 unwrap()之前测试错误，否则会发生 panic。</valueu0002c>

获取字符串的另一种方式是在&str 或 String 本身上调用 parse()。在这种情况下，你使用的是一个稍微奇怪的语法，被昵称为“涡轮鱼”，看起来像这样：

```
use std::str::FromStr;
let value_as_str = "12345";
let value = value_as_str.parse::<i32>().unwrap(); 
```

字符串的 parse()实现是一个泛型，可以与任何实现了 FromStr 的类型一起使用。因此，调用 parse::<i32>等同于调用 i32::from_str()。

Rust 的一个立即优势是它使用字符串切片。这意味着你可以有一个由分隔符分隔的长字符串，并且直接从其中间解析出数字，而不构造中间副本。

### 在不同数值类型之间转换

在不同数值类型之间转换就像使用"as"关键字一样容易。

```
let f = 1234.42f32;
let i = f as i32;
println!("Value = {}", i); 
```

结果中的 i 是 f 的整数部分。

```
Value = 1234 
```

## 字符串

Rust 附带了一些非常强大的函数，它们附加在每个&str 和 String 类型上。这些基本上对应于你可能在 std::string 类和 boost 字符串算法中习惯的内容。

大多数 Rust 中的查找 / 匹配 / 剪切 / 拆分字符串操作都很高效，因为它们既不修改现有字符串，也不将副本返回给您。相反，它们返回切片，即指向现有字符串的指针和长度，以表示结果的范围。

仅修改字符串内容本身的操作才会返回字符串的新副本，例如创建大写或小写版本。

### 修剪字符串

可以从字符串中修剪空格、制表符和其他 Unicode 中定义的空白字符。

所有字符串都可以访问以下函数

```
fn trim(&self) -> &str
fn trim_left(&self) -> &str
fn trim_right(&self) -> &str 
```

注意这些函数的签名 - 它们是不可变的。函数返回一个字符串的切片，该切片不包括删除的前导和 / 或尾随空白。换句话说，它不是复制字符串，也不是修改现有字符串。相反，它只是告诉您在您已经查看的 &str 中修剪的范围是什么。

所以

```
let untrimmed_str = " this is test with whitespace    \t";
let trimmed_str = untrimmed_str.trim();
println!("Trimmed str = \"{}\"", trimmed_str); 
```

产生：

```
Trimmed str = "this is test with whitespace" 
```

还要注意，上面的 `trim_left()` 和 `trim_right()` 受到字符串方向性的影响。

大多数字符串从左到右读取，但阿拉伯语或希伯来语中的字符串从右到左读取，并且将以设置其基本方向为从右到左的控制字符开头。如果存在该字符，则 `trim_left()` 实际上会从右侧修剪，而 `trim_right()` 会从左侧修剪。

### 获取字符串的长度

每个 &str 和 String 都有一个 len() 函数。

```
let message = "All good things come to those who wait";
println!("Length = {}", message.len()); 
```

请注意，len() 是以字节为单位的长度。如果要获取字符数，需要调用 message.chars().count()，例如

```
let message = "文字列の長さ";
assert_eq!(message.chars().count(), 6); 
```

### 拆分字符串

字符串切片和字符串具有各种 `split` 方法，返回字符串的可迭代切片集合：

```
let input = "20,30,400,100,21,-1";
let values : Vec<&str> = input.split(",").collect();
for (i, s) in values.iter().enumerate() {
    println!("Value {} = {}", i, s);
} 
```

标准的 `split()` 接受字符串模式作为分隔符，并返回一个 `std::str::Split` 结构体，该结构体是匹配结果的双端迭代器表示。如果愿意，我们可以直接调用迭代器，但是上面的 `collect()` 方法将迭代器的值放入 `Vec<&str>` 中。

```
Value 0 = 20
Value 1 = 30
Value 2 = 400
Value 3 = 100
Value 4 = 21
Value 5 = -1 
```

也可以根据索引拆分字符串，例如

```
let (left, right) = "No Mister Bond I expect you to die".split_at(14);
println!("Left = {}", left);
println!("Right = {}", right); 
```

请注意索引是 *字节索引*！如果索引位于 UTF-8 代码点的中心，则函数将会崩溃。

另一个有用的函数是 `split_whitespace`，它在制表符、空格、换行符和其他 Unicode 空白上拆分。任何数量的空白都被视为单个分隔符。

```
// Split whitespace
for s in " All good   \n\n\tthings  to those who    wait".split_whitespace() {
    println!("Part - {}", s);
} 
```

产生输出。

```
Part - All
Part - good
Part - things
Part - to
Part - those
Part - who
Part - wait 
```

### 对字符串进行标记化

待办事项

### 将字符串连接在一起

待办事项

### 获取子字符串

待办事项

### 在大写和小写之间转换字符串

字符串具有以下用于在大写和小写之间转换的函数：

```
fn to_lowercase(&self) -> String
fn to_uppercase(&self) -> String 
```

这些函数将返回一个包含输入的大写或小写版本的新字符串。大写和小写由 Unicode 规则定义。没有大写或小写字符串的语言可能会返回相同的字符。

### 执行不区分大小写的比较

待办事项

### 使用正则表达式匹配

待办事项

## 日期和时间

### 获取当前日期和时间

待办事项 time_rs

### 世界协调时间

TODO 解释 UTC 是什么以及为什么在 UTC 中维护时间是至关重要的时代等。TODO 前言关于什么是时代，Unix 时代和其他时代

### 设置计时器

TODO 设置计时器

### 系统时间 vs UTC

TODO 设置计时器可能设置在系统正常运行时间上，也可能设置在 UTC 时间上的原因。答案是因为用户和 NTP 可以更改 UTC 时间，而系统时间是相对于启动的。因此，设置一个计时器在系统时间上运行 10 秒将始终有效，而在 UTC 中运行 10 秒的计时器可能会失败，如果操作系统将时间向后调整一个小时的话。

### 将日期格式化为字符串

TODO 标准日期格式化 UTC TODO 示例

### 从字符串中解析日期

TODO 从字符串中解析日期的 TODO 示例

### 执行日期/时间运算

## 集合

### 创建静态数组

数组原语由类型和长度组成。例如，可以像这样创建并将 16 千字节的字节数组归零：

```
let values: [u8; 16384] = [0; 16384]; 
```

变量指定类型和长度，赋值运算符将 0 分配给每个元素。

类型、长度和值可以像这样隐式地就地初始化： 

```
let my_array = [ "Cat", "Dog", "Fish", "Donkey", "Albatross" ];
println!("{:?}", my_array); 
```

这是一个包含 5 个 &str 值的数组。如果我们尝试在数组中混合类型，编译器将会抱怨。我们也可以声明数组并对其进行操作：

```
let mut my_array: [&'static str; 5] = [""; 5];
// Set some values
my_array[0] = "Cat";
my_array[1] = "Dog";
my_array[2] = "Fish";
my_array[3] = "Donkey";
my_array[4] = "Albatross";
println!("{:?}", my_array); 
```

注意，在这种情况下，我们声明了数组，每个元素都获得了一个空值。然后我们的代码以编程方式设置了新元素的值。后一种形式显然对于会变化的数组是有用的。后者对于不变的数组是有用的。

### 创建动态向量

向量是一组值的线性数组。与长度固定的数组不同，向量可以随时间增长或缩小。

可以使用 vec! 宏创建一个向量，如下所示：

```
let mut my_vector = vec![1984, 1985, 1988, 1995, 2001]; 
```

这将创建一个可变的 Vec，并使用 5 个值进行预填充。请注意，vec! 宏可以使用方括号作为其参数。我们也可以使用圆括号，它的意思是一样的。

可以使用 Vec::new() 或 Vec::with_capacity(size) 创建一个新的 Vec

```
let mut my_array = Vec::new();
my_array.push("Hello");
let my_presized_array = Vec::with_capacity(100); 
```

强烈建议您使用 Vec::with_capacity() 创建一个容量足够的向量，以容纳您预期的最大元素数量。如果您不断超出现有容量，它会阻止运行时重新分配和复制数据。它还会显著减少堆碎片化。

### 从向量中移除值

有时您想要从匹配某些条件的列表中剥离值。在这种情况下，有一个方便的函数可用于此目的。TODO `.retain`

### 对向量进行排序

可以按照其包含的元素的自然排序顺序对向量进行排序：

```
let mut values = vec![ 99, -1, 3, 555, 76];
values.sort();
println!("Values = {:?}", values); 
```

排序是使用 Ord trait 进行的，并在元素上调用 Ord::cmp() 进行彼此比较。

也可以通过闭包和 Vec::sort_by() 进行比较

TODO `.sort_by` TODO `.sort_by_key`

### 从向量中剥离重复项

假设您的 vec 已经排序，您可以使用 dedup() 剥离连续重复的条目。如果您的向量没有排序，此函数将无法正常工作，结果将是未定义的。TODO .dedup

### 创建链表

当预计会从列表的两端或列表内部的点插入或删除项目时，链表比向量更适合。

`std::collections::LinkedList`

### 创建哈希集

哈希集是一组唯一对象。它特别适用于消除输入中可能出现的重复项。`std::collections::HashSet`

### 创建哈希映射

哈希映射由键和值组成。用于查找操作 `std::collections::HashMap`

### 迭代集合

待办事项

### 迭代器适配器

待办事项

适配器将迭代器转换为一个新值

`.enum` `.map(X)` `.take(N)` `.filter(X)`

### 消费迭代器

消费者是一种方便的方式，可以从结果中迭代集合并产生一个值或一组值。

`.collect()`

`.find()` 将返回与闭包谓词匹配的第一个匹配元素。待办事项

`.fold()` 是在集合上执行计算的一种方式。它接受一个基础值，然后调用一个闭包来根据上一个值的结果累积值。待办事项 处理集合

## 本地化

### Unicode 注意事项

待办事项

### 外部化字符串

待办事项

### 从参数构建字符串

待办事项

### 创建本地化文件

待办事项

## 日志记录

## 文件和流

Rust 自带两个标准模块：

+   std::io 包含各种与流相关的特性和其他功能。

+   std::fs 包含与文件系统相关的功能，包括实现 IO 特性以处理文件。

### 创建目录

可以使用 `std::fs::DirBuilder` 创建目录，例如

```
let result = DirBuilder::new().recursive(true).create("/tmp/work_dir"); 
```

### 文件路径

Windows 和 Unix 系统对路径分隔符有不同的表示法，以及许多其他差异。例如，Windows 有驱动器号、长路径和称为 UNCs 的网络路径。

Rust 提供了 PathBuf 结构体来操纵路径，以及 Path，它像一个切片，可以是完整路径或部分路径。

待办事项 简单示例，创建路径

待办事项 简单示例，Path 切片的实际应用

待办事项 简单示例，将相对路径转换为绝对路径

Windows 有一堆路径前缀，因此 std::path::Prefix 提供了一种访问这些前缀的方式。

待办事项 从驱动器号和路径创建路径的示例

### 打开文件

`File` 是对文件系统上打开的文件的引用。当结构体超出范围时，文件将关闭。有用于创建或打开文件的静态函数：

```
use std::io::prelude::*;
use std::fs::File;

let mut f = try!(File::open("myfile.txt"));
TODO 
```

注意 File::open() 默认只读打开文件。要以读写模式打开文件，有一个 OpenOptions 结构体，其中有方法来设置打开文件的行为 - 读取、写入、创建、追加和截断。

例如，以读/写访问权限打开文件，如果文件不存在则创建它。

```
use std::fs::OpenOptions;

let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open("myfile.txt"); 
```

### 写入文件

待办事项 简单示例，打开文件进行写入

### 从文件中读取行

待办事项 简单示例，以文本模式打开文件，打印内容

## 线程

Rust 在代码中积极执行线程安全性。如果尝试传递未标记为线程安全的数据（即实现 Sync 特性），则会收到编译错误。如果使用隐式不是线程安全的代码，例如 Rc<>，则会收到编译错误。

这种强制执行意味着 Rust 会防止数据竞争条件，但请注意它无法防止其他形式的竞争条件或死锁，例如，线程 1 等待资源 B（由线程 2 持有），而线程 2 等待资源 A（由线程 1 持有）。

### 创建线程

使用闭包创建线程很简单。

待办事项

### 等待线程完成

待办事项

### 使用原子引用计数

Rust 提供两种引用计数类型。类型 Rc<> 用于在同一线程上运行的代码，因此引用计数不是原子的。类型 Arc<> 用于在不同线程上运行的代码，引用计数是原子的。

Arc<> 只能持有派生自 Sync 的对象。每当克隆 Arc<> 或其生命周期结束时，计数器会原子递增或递减。最后一次递减至零会导致对象被删除。

待办事例

### 锁定共享资源

传递消息是防止线程共享状态的首选方式，但并非总是可能的。

因此，Rust 允许您创建互斥锁并锁定对共享数据的访问。锁定/解锁互斥锁的守卫保护数据，当守卫超出范围时，数据将被返回。

这种类型的守卫称为 TODO

### 数据竞争保护

Rust 可以保证防止数据竞争，即多个线程同时访问/写入相同数据。

但即使 Rust 也无法防止更一般的竞争条件。例如，如果两个线程锁定彼此的数据，则代码将死锁。这是任何语言都无法解决的问题。

### 等待多个线程完成

待办事项

### 将数据发送到线程

任何实现 Send 特性的结构都被视为安全发送到另一个线程。当然，这适用于

### 从线程接收数据

一个线程可以接收消息并阻塞直到接收到消息。因此，很容易创建某种类型的工作线程。

待办事项

## 网络

### 连接到服务器

待办事项

### 监听套接字

待办事项

## 与 C 交互

### 使用 libc 函数和类型

### 调用 C 库

### 生成动态库

### 调用 Win32 函数

## 常见设计模式

### 单例

单例在您的应用程序中永远只有一个实例。TODO

### 工厂

待办事项

### 观察者

待办事项

### 外观

待办事项

### 享元

待办事项

### 适配器

适配器是指我们向客户端呈现不同于代码实现的接口。这可能是为了使一些旧代码符合新的接口，或者为了管理/隐藏可能泄漏到客户端的复杂性。

由于 Rust 是一种相对较新的语言，你很可能会使用适配器模式来封装一些现有的 C 代码。在 C++ 中，适配器的常见用途是将 C 库封装在 RAII 类或类似的结构中。

待办事项
