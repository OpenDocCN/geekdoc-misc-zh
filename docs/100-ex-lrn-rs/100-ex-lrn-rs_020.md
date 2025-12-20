# 所有权

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/06_ownership.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/06_ownership.html)

如果你使用到目前为止课程中学到的知识解决了前面的练习，你的访问器方法可能看起来像这样：

```rs
impl Ticket {
    pub fn title(self) -> String {
        self.title
    }

    pub fn description(self) -> String {
        self.description
    }

    pub fn status(self) -> String {
        self.status
    }
}
```

这些方法可以编译，并且足以让测试通过，但在实际场景中它们不会让你走得很远。考虑这个片段：

```rs
if ticket.status() == "To-Do" {
    // We haven't covered the `println!` macro yet,
    // but for now it's enough to know that it prints 
    // a (templated) message to the console
    println!("Your next task is: {}", ticket.title());
}
```

如果你尝试编译它，你会得到一个错误：

```rs
error[E0382]: use of moved value: `ticket`
  --> src/main.rs:30:43
   |
25 |     let ticket = Ticket::new(/* */);
   |         ------ move occurs because `ticket` has type `Ticket`, 
   |                which does not implement the `Copy` trait
26 |     if ticket.status() == "To-Do" {
   |               -------- `ticket` moved due to this method call
...
30 |         println!("Your next task is: {}", ticket.title());
   |                                           ^^^^^^ 
   |                                value used here after move
   |
note: `Ticket::status` takes ownership of the receiver `self`, 
      which moves `ticket`
  --> src/main.rs:12:23
   |
12 |         pub fn status(self) -> String {
   |                       ^^^^ 
```

恭喜，这是你的第一个借用检查器错误！

## Rust 所有权系统的优势

Rust 的所有权系统旨在确保：

+   数据在读取过程中永远不会被变异

+   数据在变异过程中不会被读取

+   数据在被销毁后永远不会被访问

这些约束由 **借用检查器** 强制执行，这是 Rust 编译器的一个子系统，通常是 Rust 社区中笑话和模因的主题。

所有权是 Rust 的一个关键概念，也是使该语言独特的原因。所有权使 Rust 能够在 **不牺牲性能的情况下提供内存安全**。对于 Rust，以下所有事情都是真的：

1.  没有运行时垃圾回收器

1.  作为一名开发者，你很少需要直接管理内存

1.  你不能造成悬垂指针、双重释放和其他内存相关错误

类似 Python、JavaScript 和 Java 这样的语言提供了 2. 和 3.，但没有 1.

类似 C 或 C++ 这样的语言提供了 1.，但既没有 2. 也没有 3.

根据你的背景，3. 可能听起来有点晦涩：什么是“悬垂指针”？什么是“双重释放”？为什么它们是危险的？

别担心：我们将在课程剩余部分更详细地介绍这些概念。

然而，现在让我们专注于学习如何在 Rust 的所有权系统中工作。

## 所有者

在 Rust 中，每个值都有一个 **所有者**，在编译时静态确定。在任何给定时间，每个值只有一个所有者。

## 移动语义

所有权可以被转移。

如果你拥有一个值，例如，你可以将所有权转移到另一个变量：

```rs
let a = "hello, world".to_string(); // <- `a` is the owner of the String
let b = a;  // <- `b` is now the owner of the String
```

Rust 的所有权系统内置于类型系统中：每个函数都必须在其签名中声明它想要如何与其参数交互。

到目前为止，我们所有的方法和函数都 **消耗** 了它们的参数：它们获取了它们的所有权。例如：

```rs
impl Ticket {
    pub fn description(self) -> String {
        self.description
    }
}
```

`Ticket::description` 获取了它所调用的 `Ticket` 实例的所有权。

这被称为 **移动语义**：值的所有权（`self`）从调用者移动到被调用者，调用者不能再使用它。

这正是我们在之前的错误信息中看到的编译器使用的语言：

```rs
error[E0382]: use of moved value: `ticket`
  --> src/main.rs:30:43
   |
25 |     let ticket = Ticket::new(/* */);
   |         ------ move occurs because `ticket` has type `Ticket`, 
   |                which does not implement the `Copy` trait
26 |     if ticket.status() == "To-Do" {
   |               -------- `ticket` moved due to this method call
...
30 |         println!("Your next task is: {}", ticket.title());
   |                                           ^^^^^^ 
   |                                 value used here after move
   |
note: `Ticket::status` takes ownership of the receiver `self`, 
      which moves `ticket`
  --> src/main.rs:12:23
   |
12 |         pub fn status(self) -> String {
   |                       ^^^^ 
```

尤其是在我们调用 `ticket.status()` 时，会发生以下事件序列：

+   `Ticket::status` 获取了 `Ticket` 实例的所有权

+   `Ticket::status` 从 `self` 中提取 `status` 并将 `status` 的所有权转回调用者

+   其余的 `Ticket` 实例被丢弃（`title` 和 `description`）

当我们再次尝试通过 `ticket.title()` 使用 `ticket` 时，编译器会报错：现在 `ticket` 值已经消失了，我们不再拥有它，因此不能再使用它了。

要构建**有用的**访问器方法，我们需要开始使用**引用**。

## 借用

有方法可以读取变量的值而不获取其所有权是很有用的。

否则编程将会相当受限。在 Rust 中，这是通过**借用**来实现的。

每当你借用一个值时，你都会得到它的**引用**。

引用被标记为它们的权限^(1)：

+   不可变引用 (`&`) 允许你读取值，但不能修改它

+   可变引用 (`&mut`) 允许你读取和修改值

回到 Rust 所有权系统的目标：

+   数据在读取时永远不会被修改

+   数据在修改时永远不会被读取

为了确保这两个特性，Rust 必须对引用引入一些限制：

+   你不能同时拥有对同一值的可变引用和不可变引用

+   你不能同时拥有对同一值的多个可变引用

+   当值被借用时，所有者不能修改该值

+   只要没有可变引用，你可以拥有任意多的不可变引用

从某种意义上说，你可以将不可变引用视为对值的“只读”锁，而可变引用则像“读写”锁。

所有这些限制都由借用检查器在编译时强制执行。

### 语法

实际上，你是如何借用一个值的？

通过在变量前添加 `&` 或 `&mut` **符号**，你是在借用它的值。不过要小心！在类型**前面**的相同符号 (`&` 和 `&mut`) 有不同的意义：它们表示不同的类型，是对原始类型的引用。

例如：

```rs
struct Configuration {
    version: u32,
    active: bool,
}

fn main() {
    let config = Configuration {
        version: 1,
        active: true,
    };
    // `b` is a reference to the `version` field of `config`.
    // The type of `b` is `&u32`, since it contains a reference to 
    // a `u32` value.
    // We create a reference by borrowing `config.version`, using 
    // the `&` operator.
    // Same symbol (`&`), different meaning depending on the context!
    let b: &u32 = &config.version;
    //     ^ The type annotation is not necessary, 
    //       it's just there to clarify what's going on
}
```

同样的概念也适用于函数参数和返回类型：

```rs
// `f` takes a mutable reference to a `u32` as an argument, 
// bound to the name `number`
fn f(number: &mut u32) -> &u32 {
    // [...]
}
```

## 深呼吸，呼气

Rust 的所有权系统一开始可能会有些令人不知所措。

但别担心：随着练习，这会变得自然而然。

在本章的剩余部分以及整个课程中，你将会有很多练习机会，我们将多次回顾每个概念，以确保你熟悉它们，并真正理解它们是如何工作的。

在本章的结尾，我们将解释 Rust 所有权系统**为什么**被设计成这样。目前，专注于理解**如何**。将每个编译器错误视为一个学习机会！

## 练习

本节的练习位于[`03_ticket_v1/06_ownership`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/06_ownership)

* * *

1.  这是一个很好的起点，但它并没有捕捉到**完整**的图景。我们将在课程稍后进一步细化对引用的理解。↩
