# 组合器

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/07_combinators.html`](https://rust-exercises.com/100-exercises/06_ticket_management/07_combinators.html)

迭代器可以做得比 `for` 循环更多！

如果你查看 `Iterator` 特性的文档，你会找到一个**庞大**的方法集合，你可以利用这些方法以各种方式转换、过滤和组合迭代器。

让我们提及最常见的一些：

+   `map` 将函数应用于迭代器的每个元素。

+   `filter` 只保留满足谓词的元素。

+   `filter_map` 在一步中结合了 `filter` 和 `map`。

+   `cloned` 将引用迭代器转换为值迭代器，克隆每个元素。

+   `enumerate` 返回一个新的迭代器，它产生 `(index, value)` 对。

+   `skip` 跳过迭代器的前 `n` 个元素。

+   `take` 在 `n` 个元素后停止迭代器。

+   `chain` 将两个迭代器合并为一个。

这些方法被称为**组合器**。

通常它们会被**链式**组合在一起，以简洁和可读的方式创建复杂的转换：

```rs
let numbers = vec![1, 2, 3, 4, 5];
// The sum of the squares of the even numbers
let outcome: u32 = numbers.iter()
    .filter(|&n| n % 2 == 0)
    .map(|&n| n * n)
    .sum();
```

## 闭包

上面的 `filter` 和 `map` 方法发生了什么？

它们接受**闭包**作为参数。

闭包是**匿名函数**，即不是使用我们习惯的 `fn` 语法定义的函数。

它们使用 `|args| body` 语法定义，其中 `args` 是参数，`body` 是函数体。`body` 可以是一段代码块或单个表达式。例如：

```rs
// An anonymous function that adds 1 to its argument
let add_one = |x| x + 1;
// Could be written with a block too:
let add_one = |x| { x + 1 };
```

闭包可以接受多个参数：

```rs
let add = |x, y| x + y;
let sum = add(1, 2);
```

它们也可以捕获它们环境中的变量：

```rs
let x = 42;
let add_x = |y| x + y;
let sum = add_x(1);
```

如果需要，你可以指定参数的类型和/或返回类型：

```rs
// Just the input type
let add_one = |x: i32| x + 1;
// Or both input and output types, using the `fn` syntax
let add_one: fn(i32) -> i32 = |x| x + 1;
```

## `collect`

当你使用组合器完成迭代器的转换后会发生什么？

你可以使用 `for` 循环遍历转换后的值，或者将它们收集到集合中。

后者是通过 `collect` 方法实现的。

`collect` 消耗迭代器并将元素收集到你选择的集合中。

例如，你可以将偶数的平方收集到 `Vec` 中：

```rs
let numbers = vec![1, 2, 3, 4, 5];
let squares_of_evens: Vec<u32> = numbers.iter()
    .filter(|&n| n % 2 == 0)
    .map(|&n| n * n)
    .collect();
```

`collect` 对其**返回类型**是泛型的。

因此，通常你需要提供一个类型提示来帮助编译器推断正确的类型。在上面的例子中，我们注释了 `squares_of_evens` 的类型为 `Vec<u32>`。或者，你也可以使用**尖括号语法**来指定类型：

```rs
let squares_of_evens = numbers.iter()
    .filter(|&n| n % 2 == 0)
    .map(|&n| n * n)
    // Turbofish syntax: `<method_name>::<type>()`
    // It's called turbofish because `::<>` looks like a fish
    .collect::<Vec<u32>>();
```

## 进一步阅读

+   [`Iterator` 的文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html) 提供了 `std` 中迭代器可用方法的概述。

+   [`itertools` crate](https://docs.rs/itertools/) 定义了更多**组合器**用于迭代器。

## 练习

本节练习位于 [06_ticket_management/07_combinators](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/07_combinators)
