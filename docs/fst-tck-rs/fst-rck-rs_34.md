# 结构体

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/struct.html`](https://freddiehaddad.github.io/fast-track-to-rust/struct.html)

我们将创建一个类型来表示一个区间。Rust 对类型遵循标准化的命名约定，其中结构体使用 `UpperCamelCase`^(1) 来表示“类型级别”结构。因此，我们将命名我们的 `struct` 为 `Interval`。

## 定义我们的结构体

我们封闭的区间将表示要打印的行的开始和结束：

```rs
struct Interval {
    start: usize,
    end: usize,
}
```

## 定义行为

通过在 `impl` 块内定义它们来添加函数和方法：

```rs
impl Interval {
    // Methods definitions
}
```

## `new` 函数

在 Rust 中，定义一个名为 `new` 的函数来创建对象是常见的约定，我们将首先定义一个返回 `Interval` 的函数。

```rs
impl Interval {
    fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}
```

> 关键字 `Self`
> 
> 函数返回类型和函数体中的 `Self` 关键字是 `impl` 关键字后面指定的类型的别名，在这个例子中是 `Interval`。虽然可以显式指定类型，但常见的约定是使用 `Self`。
> 
> 省略 `return` 关键字和 (`;`)
> 
> 当返回值是函数中的最后一个表达式时，不需要使用 `return` 关键字。在这种情况下，分号 (`;`) 被省略。^(2)

## 方法

从我们的 rustle 程序中回忆，我们合并了重叠区间以防止打印相同的行多次。创建一个检查两个区间是否重叠的方法以及另一个合并重叠区间的方法将非常有用。让我们概述这些方法！

```rs
fn overlaps(&self, other: &Interval) -> bool {
    todo!();
}

fn merge(&self, other: &Self) -> Self {
    todo!();
}
```

> `todo!()` 和 `unimplemented!()` 宏在原型设计时非常有用，如果你只是想要一个占位符来让代码通过类型分析。

### `self` 方法接收者

你可能习惯于在类方法中使用隐式的 `this` 指针（一个隐藏的第一个参数）。在 Rust 中，使用 `self` 关键字来表示方法的接收者，并且约定省略此参数的类型。根据预期的行为，它可以指定为 `self`、`&self` 或 `&mut self`。^(3)

> 在 `self` 后面省略类型是语法糖。它等价于 `self: Self`。由于 `Self` 是实际类型的别名，完整的展开将是 `self: Interval`、`self: &Interval` 或 `self: &mut Interval`。

## 实现方法

记住，我们的 rustle 程序是按顺序处理行的。这允许我们优化重叠区间的检测。然而，这种方法限制了我们的 `Interval` 类型的通用性。作为一个练习，你可以尝试使其更加通用。

### 重叠

`overlaps` 方法相当直接。我们检查第一个区间的 `end` 是否大于或等于下一个区间的 `start`。唯一的注意事项是比较的顺序。

```rs
fn overlaps(&self, other: &Interval) -> bool {
    self.end >= other.start
}
```

### 合并

`merge` 方法使用第一个区间的 `start` 和第二个区间的 `end` 返回一个新的 `Interval`。同样，接收者必须是序列中先出现的区间。

在这两种情况下，对两个区间进行不可变借用就足够了，因为我们不需要对任何值进行修改。

```rs
fn merge(&self, other: &Self) -> Self {
    Interval::new(self.start, other.end)
}
```

### 实现 `merge_intervals`

来自 C++ 背景的 Rust 程序员可能会倾向于使用以下算法的某种变体来实现此函数：

```rs
fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
    let mut merged_intervals: Vec<Interval> = Vec::new();

    let mut iter = intervals.into_iter();
    match iter.next() {
        Some(interval) => merged_intervals.push(interval),
        None => return merged_intervals,
    };

    for interval in iter {
        if let Some(previous_interval) = merged_intervals.last() {
            if previous_interval.overlaps(&interval) {
                let new_interval = previous_interval.merge(&interval);
                merged_intervals.pop();
                merged_intervals.push(new_interval);
            } else {
                merged_intervals.push(interval);
            }
        }
    }

    merged_intervals
}
```

虽然功能上是正确的，但 Rust 提供了强大的 crate，可以使实现此行为更加简洁。其中一个这样的 crate 是 `Itertools`，它提供了额外的迭代器适配器。要使用此 crate，请在 `Crates.toml` 中将其指定为依赖项，并在 `main.rs` 中包含它，使用 `use itertools::Itertools`。让我们看看 `coalesce` 适配器如何简化代码：

```rs
use itertools::Itertools;

fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
    intervals
        .into_iter()
        .coalesce(|p, c| {
            if p.overlaps(&c) {
                Ok(p.merge(&c))
            } else {
                Err((p, c))
            }
        })
        .collect()
}
```

> `into_iter`
> 
> 在两种实现中，我们使用 `into_iter`，它创建了一个消耗性迭代器，从开始到结束将每个值从向量中移动出来。这是我们可以利用移动语义的另一个例子。
> 
> NOTE：由于迭代器消耗数据，因此之后不能使用该向量。

## 更新 Rustle

是时候更新我们的 rustle 程序以利用我们的新类型了。此外，还进行了一些小的更改，以增强设计，展示一些额外的语言特性，并利用移动语义。运行一下程序吧！

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use itertools::Itertools;
use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection } 
fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Vec<Interval> {
    lines
        .iter()
        .map(|line| {
            let start = line.saturating_sub(before_context);
            let end = line.saturating_add(after_context);
            Interval::new(start, end)
        })
        .collect()
}

fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
    // merge overlapping intervals
    intervals
        .into_iter()
        .coalesce(|p, c| {
            if p.overlaps(&c) {
                Ok(p.merge(&c))
            } else {
                Err((p, c))
            }
        })
        .collect()
}

fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
    for interval in intervals {
        for (line_no, line) in lines
            .iter()
            .enumerate()
            .take(interval.end + 1)
            .skip(interval.start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
}

fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = create_intervals(match_lines, before_context, after_context);      // merge overlapping intervals
    let intervals = merge_intervals(intervals);
  // print the lines print_results(intervals, lines); }

struct Interval {
    start: usize,
    end: usize,
}

impl Interval {
    fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    fn overlaps(&self, other: &Interval) -> bool {
        self.end >= other.start
    }

    fn merge(&self, other: &Self) -> Self {
        Interval::new(self.start, other.end)
    }
}
```

## 总结更改

我们现在使用的 rustle 程序利用了我们的自定义类型，并包含了一些其他增强功能。

让我们回顾一下更改：

`create_intervals` 已更新，具体更改如下：

+   返回类型已更改为 `Vec<Interval>`

+   由 `start` 和 `end` 创建的元组现在用于创建一个 `Interval`

`merge_intervals` 已更新，具体更改如下：

+   参数 `intervals` 现在的类型为 `Vec<Interval>`，并且是 *移动* 而不是可变借用

+   `dedup_by` 已被 `coalesce` 替换

`print_results` 已更新，具体更改如下：

+   参数 `intervals` 现在是 `Vec<Interval>`

+   `take` 和 `skip` 迭代器适配器已更新，以使用 `Interval` 的字段

> 在将每个区间作为 `for interval in intervals` 写入时，循环迭代结束时都会 *丢弃* 区间。如果循环写成 `for interval in &intervals`，我们会 *借用* 每个值。同样，如果我们将其写成 `for interval in intervals.iter()`，也是这样。前者是后者的语法糖。⁴

* * *

1.  命名约定符合 [RFC 430](https://github.com/rust-lang/rfcs/blob/master/text/0430-finalizing-naming-conventions.md) (C-CASE)。↩

1.  关于 `return` 的排除在此处讨论。↩

1.  方法语法在[这里](https://doc.rust-lang.org/book/ch05-03-method-syntax.html)有详细的介绍。↩

1.  关于使用 `for in` 和 `into_iter` 消费集合的详细信息可以在[这里](https://doc.rust-lang.org/rust-by-example/flow_control/for.html)找到。↩
