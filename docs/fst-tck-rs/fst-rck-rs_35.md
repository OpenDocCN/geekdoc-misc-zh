# 枚举

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/enum.html`](https://freddiehaddad.github.io/fast-track-to-rust/enum.html)

一个*[枚举](https://doc.rust-lang.org/reference/items/enumerations.html)*，通常称为*[枚举类型](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html)*，使用关键字`enum`进行声明。与其它语言相比，Rust 中的枚举提供了更大的灵活性和功能。例如，它们支持泛型（如`Option`枚举所示）并且可以在其变体中封装值！^(1)

## 使用枚举处理错误

对于我们的 rustle 程序，我们将创建一个枚举来表示在`Interval`操作期间可能出现的错误。例如，当用户创建一个`Interval`时，起始值必须小于或等于结束值。此外，如果用户想要合并两个区间，它们必须重叠。如果这些条件不满足，我们将使用我们的枚举变体之一返回错误（`Err`）。

## 定义枚举

下面是`IntervalError`枚举，它列出了我们可能需要返回的错误：

```rs
enum IntervalError {
    StartEndRangeInvalid,
    NonOverlappingInterval,
}
```

## 更新我们的区间

首先，我们将函数`new`和方法`merge`的返回类型更改为`Result`类型，其中`Ok`变体是`Interval`，而`Err`变体是适当的`IntervalError`：

```rs
fn new(start: usize, end: usize) -> Result<Self, IntervalError> {
    if start <= end {
        Ok(Self { start, end })
    } else {
        Err(IntervalError::StartEndRangeInvalid)
    }
}
```

```rs
fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
    if self.overlaps(other) {
        Ok(Self {
            start: self.start,
            end: other.end,
        })
    } else {
        Err(IntervalError::NonOverlappingInterval)
    }
}
```

> 观察到`Interval`是在`new`中创建的，而不是在`merge`中。由于`new`中的参数名称与`Interval`结构定义中的字段完全匹配，因此可以省略字段指定符。这种技术被称为*字段初始化简写*语法。^(2)

## 更新 Rustle

在实现了`Interval`更改后，我们需要更新`create_intervals`和`merge_intervals`函数以适应`Result`返回类型。

```rs
fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Result<Vec<Interval>, IntervalError> {
    lines
        .iter()
        .map(|line| {
            let start = line.saturating_sub(before_context);
            let end = line.saturating_add(after_context);
            Interval::new(start, end)
        })
        .collect()
}
```

在`create_intervals`中，唯一的变化是返回类型，它从`Vec<Interval>`更改为`Result<Vec<Interval>, IntervalError>`。你可能会想知道为什么这行得通。简洁的答案是`Result`类型实现了`FromIterator`特质。

想象一下，从对`Interval::new(start, end)`的调用中创建了一个中间的`Result`值集合。`FromIterator`特质的实现允许对`Result`值的迭代器进行收集，*进入*一个包含底层值集合或`Err`的`Result`。换句话说，`Interval::new(start, end)`返回的`Result`中的值存储在`Vec<Interval>`集合中，然后被`Result`包装。

> 在下一节中，我们将探讨特质。

```rs
fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
    // merge overlapping intervals
    intervals
        .into_iter()
        .coalesce(|p, c| p.merge(&c).or(Err((p, c))))
        .collect()
}
```

在 `merge_intervals` 中，所需更改仅限于 `coalesce` 中使用的闭包。我们尝试合并两个区间，并调用 `Result` 的 `or` 方法。如果合并成功，返回 `Ok`，并将值传递回 `coalesce`。否则，返回给 `or` 的 `Err((p, c))` 值。

> `Result` 方法如 `map_err`、`or` 和 `or_else` 常用于错误处理，因为它们允许管理良性错误，同时让成功的结果通过。由于 `merge` 方法只合并重叠的区间，我们用 `coalesce` 所需的元组 `(p, c)` 替换了它返回的 `Err` 变体。
> 
> 贪婪评估 vs 惰性评估
> 
> 根据用例，不同的 `Result` 方法可能更高效。阅读文档以确定最佳选择很重要。例如，传递给 `or` 的参数会被贪婪评估。[`or`](https://doc.rust-lang.org/std/result/enum.Result.html#method.or)。如果你传递的是函数调用的结果，最好使用 `or_else`，它是惰性评估的。

需要做的最后一个更改是在 `main` 中。由于 `create_intervals` 现在返回 `Result`，我们使用 `match` 表达式来检查操作是否成功。在 `Err` 的情况下，由于它是不可恢复的，我们打印错误消息并退出。

```rs
// create intervals of the form [a,b] with the before/after context
let intervals =
    match create_intervals(match_lines, before_context, after_context) {
        Ok(intervals) => intervals,
        Err(_) => {
            eprintln!("An error occurred while creating intervals");
            exit(1);
        }
    };
```

# 更新 Rustle

在我们做出更改后，我们的 Interval 现在支持通过 `Result` 进行错误处理，并且我们的 rustle 程序正确处理了任何错误。

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Result<Vec<Interval>, IntervalError> {
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
        .coalesce(|p, c| p.merge(&c).or(Err((p, c))))
        .collect()
}

fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);      // create intervals of the form [a,b] with the before/after context
    let intervals =
        match create_intervals(match_lines, before_context, after_context) {
            Ok(intervals) => intervals,
            Err(_) => {
                eprintln!("An error occurred while creating intervals");
                exit(1);
            }
        };
  // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }

enum IntervalError {
    StartEndRangeInvalid,
    NonOverlappingInterval,
}

struct Interval {
    start: usize,
    end: usize,
}

impl Interval {
    fn new(start: usize, end: usize) -> Result<Self, IntervalError> {
        if start <= end {
            Ok(Self { start, end })
        } else {
            Err(IntervalError::StartEndRangeInvalid)
        }
    }

    fn overlaps(&self, other: &Interval) -> bool {
        self.end >= other.start
    }

    fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
        if self.overlaps(other) {
            Ok(Self {
                start: self.start,
                end: other.end,
            })
        } else {
            Err(IntervalError::NonOverlappingInterval)
        }
    }
}
```

# 总结

在 Rust 中使用 `Result` 类型进行错误处理的决定提供了一种强大且灵活的错误管理方式，例如：

1.  **显式错误处理**：使用 `Result` 使错误处理变得显式。可能失败的函数返回 `Result`，这迫使调用者处理潜在的错误，使代码更可靠，更不容易出现意外的失败。

1.  **可恢复的错误**：`Result` 类型允许可恢复的错误。通过返回 `Result`，函数给调用者提供了以适合其特定上下文的方式处理错误的选择，而不是立即终止程序。

1.  **类型安全**：Rust 的类型系统确保错误被正确处理。`Result` 类型是这个系统的一部分，有助于防止常见的错误，如空指针解引用，并使代码更安全、更可预测。

1.  **可组合性**：`Result` 类型实现了 `FromIterator` 等特质，这允许强大的灵活的错误处理模式。这使得处理结果集合和通过多层函数调用传播错误变得更容易。

总体而言，使用 `Result` 与 Rust 的目标（安全性、并发性和性能）相一致，提供了一种清晰和结构化的错误处理方式。

# 练习

+   在`merge_intervals`中将`Result::or`替换为`Result::map_err`。

    <details><summary>解决方案</summary>

    ```rs
    fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
        // merge overlapping intervals
        intervals
            .into_iter()
            .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c)))
            .collect()
    }
    ```</details>

```rs
#![allow(unused_imports)]
extern crate regex; // this is needed for the playground
use itertools::Itertools;
use regex::Regex;
use std::fs::File;
use std::io::Read;
use std::io::{BufRead, BufReader};
use std::process::exit;

fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match regex.is_match(line) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
}

fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Result<Vec<Interval>, IntervalError> {
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
        .coalesce(|p, c| p.merge(&c).or(Err((p, c))))
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
    BufReader::new(file).lines().map_while(Result::ok).collect()
}

fn main() {
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";

    let mock_file = std::io::Cursor::new(poem);

    // command line arguments
    let pattern = "(all)|(little)";
    let before_context = 1;
    let after_context = 1;

    // attempt to open the file
    let lines = read_file(mock_file);
    //let lines = match File::open(filename) {
    //    // convert the poem into lines
    //    Ok(file) => read_file(file),
    //    Err(e) => {
    //        eprintln!("Error opening {filename}: {e}");
    //        exit(1);
    //    }
    //};

    // compile the regular expression
    let regex = match Regex::new(pattern) {
        Ok(re) => re, // bind re to regex
        Err(e) => {
            eprintln!("{e}"); // write to standard error
            exit(1);
        }
    };

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(&lines, regex);

    // create intervals of the form [a,b] with the before/after context
    let intervals =
        match create_intervals(match_lines, before_context, after_context) {
            Ok(intervals) => intervals,
            Err(_) => {
                eprintln!("An error occurred while creating intervals");
                exit(1);
            }
        };

    // merge overlapping intervals
    let intervals = merge_intervals(intervals);

    // print the lines
    print_results(intervals, lines);
}

enum IntervalError {
    StartEndRangeInvalid,
    NonOverlappingInterval,
}

struct Interval {
    start: usize,
    end: usize,
}

impl Interval {
    fn new(start: usize, end: usize) -> Result<Self, IntervalError> {
        if start <= end {
            Ok(Self { start, end })
        } else {
            Err(IntervalError::StartEndRangeInvalid)
        }
    }

    fn overlaps(&self, other: &Interval) -> bool {
        self.end >= other.start
    }

    fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
        if self.overlaps(other) {
            Ok(Self {
                start: self.start,
                end: other.end,
            })
        } else {
            Err(IntervalError::NonOverlappingInterval)
        }
    }
}
```

# 下一步

我们的区间（Interval）完成之后，让我们将其变成一个模块！

* * *

1.  请参考关于[枚举值](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html#enum-values)的文档。↩

1.  请参考关于*[字段初始化缩写](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-the-field-init-shorthand)*语法的文档。↩

1.  请参考关于[收集到`Result`中](https://doc.rust-lang.org/std/result/#collecting-into-result)的文档以获取详细解释。↩
