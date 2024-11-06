# 使用模块进行命名空间

# 使用模块进行命名空间

C++ 的命名空间允许你将函数、变量和类分组到逻辑块中，并允许编译器将它们与其他可能具有相同名称的函数、变量和类加以区分。

```
// Namespacing is usually a good idea
namespace myapp {
  void error() {
    //...
  }
  const int SOME_VALUE = 20;
  void doSomething(int value) {
    //...
  }
}
//... somewhere else in the code
myapp::doSomething(100); 
```

在 C++ 中，命名空间是完全可选的，这意味着某些代码可能会使用嵌套命名空间，而其他代码可能会满足于将其整个代码库放入一个命名空间中。有些代码甚至可能将其代码放入全局命名空间中。其他代码可能会使用宏来控制命名空间的使用。

Rust 中与命名空间相当的是模块，并且起着类似的作用。但与 C++ 不同的是，你可以从文件的结构中自动获得命名空间。每个文件本身就是一个模块。

所以如果我们可能有一个文件 myapp.rs

```
// myapp.rs
pub fn error() { /* ... */ }
pub const SOME_VALUE: i32 = 20;
pub fn doSomething(value: i32) { /* ... */ } 
```

myapp.rs 中的所有内容都会自动成为一个名为 myapp 的模块。这意味着模块是隐式的，你不需要做任何事情，只需给你的文件起一个有意义的名字。

```
use myapp;
myapp::doSomething(myapp::SOME_VALUE); 
```

你也可以选择将整个模块都引入进来：

```
use myapp::*;
doSomething(SOME_VALUE); 
```

或者只是你使用的其中的类型和函数：

```
use myapp::{doSomething, SOME_VALUE}
doSomething(SOME_VALUE);
// Other bits can still be referenced by their qualifying mod
myapp::error(); 
```

但如果你想要一个显式模块，你也可以在代码中编写它。所以也许 myapp 并不适合作为一个单独的文件。

```
// main.rs
mod myapp {
  pub fn error() { /* ... */ }
  pub const SOME_VALUE = 20;
  pub fn doSomething(value: i32) { /* ... */ }
} 
```

模块可以嵌套，因此可以同时使用隐式模块（来自文件名）和显式模块。

## 跨文件拆分模块

使用模块进行命名空间相当简单，但有时你可能有很多文件在一个模块中，而你不希望外界看到单个模块命名空间。

在这些情况下，你更可能使用 myapp/mod.rs 形式。在这种情况下，mod.rs 文件可能会拉取

在从属文件中

```
// myapp/mod.rs
mod helpers;
mod gui;

#[cfg(test)]
mod tests

// Perhaps we want the outside world to see myapp::Helper
pub use helpers::Helper; 
```

在这个例子中，模块引入了子模块 `helpers` 和 `gui`。两者都没有标记为 `pub mod`，所以它们对于模块来说是私有的。

然而，模块还说 `pub use helpers::Helper`，这允许外部引用 `myapp::Helper`。因此，模块可以充当对其引用的事物的门卫，保持它们私有或选择性地公开部分内容。

我们还没有提到这里的另一个模块 `tests`。属性 `#[cfg(test)]` 表示它只在构建单元测试可执行文件时才被引入。`cfg` 属性用于[条件编译](https://doc.rust-lang.org/book/conditional-compilation.html)。

## 使用模块

定义了之后就可以使用模块。

```
use helpers::*; 
```

注意，use 命令是相对于顶层 `main` 或 `lib` 模块的。所以如果你在顶部声明了一个 `mod helpers`，那么相应的 `use helpers` 将会检索到它。你也可以使用相对 `use` 命令来使用 `super` 和 `self` 关键字。

// TODOs

## 模块别名

TODO

## 外部 crate

TODO
