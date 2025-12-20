# 变量

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/02_variables.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/02_variables.html)

在 Rust 中，你可以使用 `let` 关键字来声明**变量**。

例如：

```rs
let x = 42;
```

上面我们定义了一个变量 `x` 并将其赋值为 `42`。

## 类型

Rust 中的每个变量都必须有一个类型。它可以是编译器推断的，也可以是开发者显式指定的。

### 显式类型注解

你可以通过在变量名后添加冒号 `:` 并跟类型来指定变量类型。例如：

```rs
// let <variable_name>: <type> = <expression>;
let x: u32 = 42;
```

在上面的例子中，我们显式地将 `x` 的类型约束为 `u32`。

### 类型推断

如果我们没有指定变量的类型，编译器将尝试根据变量使用的上下文来推断它。

```rs
let x = 42;
let y: u32 = x;
```

在上面的例子中，我们没有指定 `x` 的类型。

`x` 之后被赋值给 `y`，`y` 被显式地指定为 `u32` 类型。由于 Rust 不执行自动类型转换，编译器推断 `x` 的类型为 `u32`——与 `y` 相同，并且是唯一允许程序编译无误的类型。

### 推断限制

编译器有时需要一点帮助来根据其使用情况推断正确的变量类型。

在这些情况下，你会得到一个编译错误，编译器会要求你提供一个显式的类型提示来消除歧义。

## 函数参数是变量

不是所有的英雄都穿斗篷，不是所有的变量都是用 `let` 声明的。

函数参数也是变量！

```rs
fn add_one(x: u32) -> u32 {
    x + 1
}
```

在上面的例子中，`x` 是类型为 `u32` 的变量。

`x` 和用 `let` 声明的变量之间的唯一区别是，函数参数**必须**显式声明其类型。编译器不会为你推断它。

这个约束允许 Rust 编译器（以及我们人类！）理解函数的签名，而无需查看其实现。这对编译速度有很大的提升^(1)！

## 初始化

在声明变量时，你不必初始化它。

例如

```rs
let x: u32;
```

是一个有效的变量声明。

然而，在使用变量之前，你必须初始化它。如果你不这样做，编译器会抛出错误：

```rs
let x: u32;
let y = x + 1;
```

将引发编译错误：

```rs
error[E0381]: used binding `x` isn't initialized
 --> src/main.rs:3:9
  |
2 | let x: u32;
  |     - binding declared here but left uninitialized
3 | let y = x + 1;
  |         ^ `x` used here but it isn't initialized
  |
help: consider assigning a value
  |
2 | let x: u32 = 0;
  |            +++ 
```

## 练习

本节的练习位于[`02_basic_calculator/02_variables`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/02_variables)

* * *

1.  当涉及到编译速度时，Rust 编译器需要所有它能得到的帮助。↩
