# 文件输入/输出

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/file_io.html`](https://freddiehaddad.github.io/fast-track-to-rust/file_io.html)

如果没有搜索文本文件的能力，我们的 rustle 程序将不完整。考虑到 I/O 错误的可能性，现在添加此功能很方便，因为我们正在探索错误处理和 `Result` 类型。这也让我们了解了 Rust 标准库中的其他包。

> 到目前为止，我们能够在 rustle 程序中使用字符串字面量，因为不需要动态内存分配。然而，现在我们将从文件中读取，动态内存分配变得必要。字符串切片不再足够，因此我们需要利用 Rust 中的 `String` 类型。
> 
> 在堆上存储数据
> 
> 如果你需要直接在堆上分配内存，通常使用 `Box` 类型。你可以在 [关于 `Box` 类型的文档](https://doc.rust-lang.org/book/ch15-01-box.html) 中找到其使用的许多示例。

让我们从创建一个读取文件并返回一个字符串向量 (`Vec<String>`) 的函数开始，其中每个字符串代表一行。以下是函数签名：^(1) ^(2)

```rs
fn read_file(file: File) -> Vec<String> {
    todo!(); // see the footnote [³]
}
```

这是我们将添加到 `read_file` 函数中的代码：

```rs
BufReader::new(file).lines().map_while(Result::ok).collect()
```

`read_file` 函数接受一个文件句柄，并使用 `BufReader` 有效地逐行读取文件，将每一行存储在字符串向量 (`Vec<String>`) 中，然后将其返回给调用者。

> 读取文件并将结果存储在集合中的许多低效方法通常涉及遍历每一行，将其转换为字符串，然后将字符串推送到向量中。这种方法需要中间内存分配，对于大文件来说可能会变得昂贵。此外，从文件中读取的每一行都可能涉及系统调用。`BufReader` 使用内部缓冲区从文件中读取大量数据，从而最小化内存分配和系统调用。

`main` 函数的修改：

```rs
fn main() {
    // command line arguments
 let pattern = "all"; let before_context = 1; let after_context = 1;    let filename = "poem.txt";

    // attempt to open the file
    let lines = match File::open(filename) {
        // convert the poem into lines
        Ok(file) => read_file(file),
        Err(e) => {
            eprintln!("Error opening {filename}: {e}");
            exit(1);
        }
    };
  // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, pattern);   // create intervals of the form [a,b] with the before/after context let mut intervals = create_intervals(match_lines, before_context, after_context);   // merge overlapping intervals merge_intervals(&mut intervals);   // print the lines print_results(intervals, lines); }
```

## 解包代码

这里有很多内容，让我们一步一步地分解。

### `read_file`

```rs
fn read_file(file: File) -> Vec<String> {
    BufReader::new(file).lines().map_while(Result::ok).collect()
}
```

1.  **`BufReader`**: `BufReader::new(file)` 从提供的 `File` 创建一个缓冲读取器。这有助于有效地逐行读取文件。

1.  **`lines()`**: `BufReader` 上的 `lines()` 方法返回文件中行的迭代器。由于从文件读取可能会出错，因此每行都被包装在一个 `Result` 中，该 `Result` 可以是 `Ok`（包含行内容）或 `Err`（包含错误）。

1.  **`map_while(Result::ok)`**: `map_while` 方法用于转换迭代器。它将 `Result::ok` 函数应用于每个项目，将 `Ok(line)` 转换为 `Some(line)`，将 `Err(_)` 转换为 `None`。遇到第一个 `None` 时迭代停止。以下是 [源代码](https://doc.rust-lang.org/std/result/enum.Result.html) 的相关部分，为了可读性进行了整理：

    ```rs
    pub enum Result<T, E> {
       Ok(T),
       Err(E),
    }

    impl<T, E> Result<T, E> {
        pub fn ok(self) -> Option<T> {
            match self {
                Ok(x) => Some(x),
                Err(_) => None,
            }
        }
    }
    ```

    这种转换是必要的，因为 map 方法需要闭包返回一个 `Option`。将 `Err` 转换为 `None` 会丢弃错误值，并导致 `map_while` 停止产生。

1.  **`collect()`**: `collect()` 方法将所有 `Some(line)` 值收集到一个返回给调用者的 `Vec<String>` 中。

### main

在 `main` 函数中，我们尝试打开一个文件，这可能由于各种原因而失败。如果 `Result` 是 `Ok`，我们使用文件值调用 `read_file`。由于我们之后不需要文件句柄，因此不需要借用。如果在打开文件时发生错误，我们使用 `eprintln!` 宏将错误打印到标准错误，然后退出。

## 整合一切

这里是隐藏了程序无关部分的更改：

```rs
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::process::exit;
  fn find_matching_lines(lines: &[String], pattern: &str) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match line.contains(pattern) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Vec<(usize, usize)> {
 lines .iter() .map(|line| { ( line.saturating_sub(before_context), line.saturating_add(after_context), ) }) .collect() }   fn merge_intervals(intervals: &mut Vec<(usize, usize)>) {
 // merge overlapping intervals intervals.dedup_by(|next, prev| { if prev.1 < next.0 { false } else { prev.1 = next.1; true } }) }   fn print_results(intervals: Vec<(usize, usize)>, lines: Vec<String>) {
 for (start, end) in intervals { for (line_no, line) in lines.iter().enumerate().take(end + 1).skip(start) { println!("{}: {}", line_no + 1, line) } } } 
fn read_file(file: File) -> Vec<String> {
    BufReader::new(file).lines().map_while(Result::ok).collect()
}

fn main() {
    // command line arguments
 let pattern = "all"; let before_context = 1; let after_context = 1;    let filename = "poem.txt";

    // attempt to open the file
    let lines = match File::open(filename) {
        // convert the poem into lines
        Ok(file) => read_file(file),
        Err(e) => {
            eprintln!("Error opening {filename}: {e}");
            exit(1);
        }
    };
  // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, pattern);   // create intervals of the form [a,b] with the before/after context let mut intervals = create_intervals(match_lines, before_context, after_context);   // merge overlapping intervals merge_intervals(&mut intervals);   // print the lines print_results(intervals, lines); }
```

> 不要忘记，你可以通过点击 *显示隐藏行* 来揭示隐藏的部分。

# 摘要

+   Rust 需要在代码编译前承认和处理错误，以确保稳健性。

+   错误被分为可恢复的（例如，文件未找到）和不可恢复的（例如，越界访问）。

+   Rust 使用 `Result<T, E>` 来处理可恢复的错误，并使用 `panic!` 来处理不可恢复的错误，这与使用异常的其他语言不同。

# 下一页

要继续使用 Rust Playground，打开实际文件是不行的。让我们看看我们如何利用内存缓冲区来表示一个打开的文件。

* * *

1.  在 Rust 中，字符串实现为 `Vec<u8>`。有关详细信息，请参考 [API](https://doc.rust-lang.org/stable/std/string/index.html)。 ↩

1.  不幸的是，Rust Playground 不支持打开文件，因此你需要在你本地机器上运行这段代码。 ↩

1.  Rust 提供了几个有用的宏，这些宏对于开发和原型设计你的程序非常有用。其中之一是 `todo!()`（[todo!()](https://doc.rust-lang.org/std/macro.todo.html)），另一个是 `unimplemented!()`（[unimplemented!()](https://doc.rust-lang.org/std/macro.unimplemented.html)）。 ↩
