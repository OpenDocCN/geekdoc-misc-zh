# 命令行参数

> [原文链接](https://freddiehaddad.github.io/fast-track-to-rust/clap.html)

在 `Cargo.toml` 部分中，你被要求添加 `clap`（[链接](https://crates.io/crates/clap)）crate 作为依赖项以支持我们的 rustle 程序的命令行参数解析。根据我们对属性的当前理解，现在是利用这个 crate 通过扩展我们的 rustle 程序来处理命令行参数的理想时机。

使用 `clap` 定义命令行参数的一种方法涉及使用自定义属性。这就是为什么我们在依赖项中指定了 derive 功能。

如果你没有完成练习并且在本地上正在学习这门课程，你可以通过以下方式将依赖项添加到 rustle crate 中：

```rs
$ cargo add clap --features derive 
```

## 高级属性

关于 [宏属性](https://doc.rust-lang.org/reference/procedural-macros.html#attribute-macros) 和 [derive 宏辅助属性](https://doc.rust-lang.org/reference/procedural-macros.html#derive-macro-helper-attributes) 的主题相当高级，超出了本课程的范畴。因此，我们不会深入探讨它们的内部工作原理。然而，在你继续 Rust 之旅时，请记住这一部分，因为很可能你将需要自己实现类似的属性以进行代码生成。

## 扩展 rustle

我们将向我们的程序添加命令行参数支持。然而，我们将继续模拟命令行参数以保持这门课程在线开发。在配置 `clap` 之后，这将自动生成的帮助信息（即在终端中输入 `rustle --help`）。

```rs
$ rustle.exe --help
Usage: rustle.exe [OPTIONS] <PATTERN> [FILES]...

Arguments:
  <PATTERN>   The regular expression to match
  [FILES]...  List of files to search

Options:
  -l, --line-number           Prefix each line of output with the 1-based line
                              number within its input file
  -b, --before-context <num>  Print num lines of trailing context before matching
                              lines [default: 0]
  -a, --after-context <num>   Print num lines of trailing context after matching
                              lines [default: 0]
  -h, --help                  Print help
  -V, --version               Print version 
```

> `CLAP` 文档非常详尽，包含了许多学习示例。如果你在构建 CLI 应用程序，你肯定会想参考[文档](https://crates.io/crates/clap)。

这是添加了命令行参数支持的 rustle 的更新版本：

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use clap::Parser;
use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::path::PathBuf;
use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval<usize>>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() } 
fn print_results(
    intervals: Vec<Interval<usize>>,
    lines: Vec<String>,
    line_number: bool,
) {
    for interval in intervals {
        for (line_no, line) in lines
            .iter()
            .enumerate()
            .take(interval.end + 1)
            .skip(interval.start)
        {
            if line_number {
                print!("{}: ", line_no + 1);
            }
            println!("{}", line);
        }
    }
}
  fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() } 
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Prefix each line of output with the 1-based line number within its
    /// input file.
    #[arg(short, long, default_value_t = false)]
    line_number: bool,

    /// Print num lines of trailing context before matching lines.
    #[arg(short, long, default_value_t = 0, value_name = "num")]
    before_context: u8,

    /// Print num lines of trailing context after matching lines.
    #[arg(short, long, default_value_t = 0, value_name = "num")]
    after_context: u8,

    /// The regular expression to match.
    #[arg(required = true)]
    pattern: String,

    /// List of files to search.
    #[arg(required = true)]
    files: Vec<PathBuf>,
}

fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);      // let cli = Cli::parse(); // for production use
    // mock command line arguments
    let cli = match Cli::try_parse_from([
        "rustle", // executable name
        "--line-number",
        "--before-context",
        "1",
        "--after-context",
        "1",
        "(all)|(little)", // pattern
        "poem.txt",       // file
    ]) {
        Ok(cli) => cli,
        Err(e) => {
            eprintln!("Error parsing command line arguments: {e:?}");
            exit(1);
        }
    };

    // get values from clap
    let pattern = cli.pattern;
    let line_number = cli.line_number;
    let before_context = cli.before_context as usize;
    let after_context = cli.after_context as usize;
  // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(&pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals); 
    // print the lines
    print_results(intervals, lines, line_number);
}
  pub mod interval {
 /// A list specifying general categories of Interval errors. #[derive(Debug)] pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ #[derive(Debug, PartialEq)] pub struct Interval<T> { pub start: T, pub end: T, }   impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } }   use std::fmt; impl<T: fmt::Display> fmt::Display for Interval<T> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result { write!(f, "[{}, {}]", self.start, self.end) } }   use std::cmp::Ordering; impl<T: PartialEq + PartialOrd> PartialOrd for Interval<T> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { if self == other { Some(Ordering::Equal) } else if self.end < other.start { Some(Ordering::Less) } else if self.start > other.end { Some(Ordering::Greater) } else { None // Intervals overlap } } } }
```

# 摘要

我们在配置 `clap` 的同时做了一些小的代码更改。其中大部分现在应该都很直接，所以我们将关注新的方面：

+   `PathBuf` 模块简化了跨平台的路径操作。由于我们的 rustle 程序需要搜索文件，因此使用 `PathBuf` 来处理这些输入会更好。

+   我们更新了 `print_results`，使其接受一个新的布尔参数 `line_number`，该参数指定是否在输出中打印行号。如果为 `true`，则使用 `print!` 宏输出行号而不输出换行符。

+   我们使用 `clap` 属性来推导我们的命令行参数。`clap` [文档](https://crates.io/crates/clap) 详细介绍了这些属性。

+   在 `main` 中，我们使用一个字符串切片数组模拟命令行参数，该数组由 `clap` 解析。

    > `match` 表达式仅用于开发目的。如果我们对模拟的命令行参数有任何错误，我们会捕获错误并打印出来。

+   由于我们在 `Cli` 结构体中将 `before_context` 和 `after_context` 变量定义为 `u8`，但在整个代码中使用 `usize`，因此在将这些值赋给局部变量时需要使用 `as` [关键字](https://doc.rust-lang.org/std/keyword.as.html) 进行显式转换。

# 下一页

前进到并发编程！
