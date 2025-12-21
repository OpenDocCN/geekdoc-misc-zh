# 多线程 Rustle

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/multithreaded_rustle.html`](https://freddiehaddad.github.io/fast-track-to-rust/multithreaded_rustle.html)

通过对作用域线程与非作用域线程的理解，我们现在准备正确更新 rustle，以便在单独的线程中处理命令行上指定的每个文件。

这是程序更新的版本，其中可见更改。

```rs
#![allow(unused_imports)] use clap::Parser; use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::collections::HashMap;
use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::path::PathBuf; use std::process::exit; use std::thread;

fn find_matching_lines(lines: &[String], regex: &Regex) -> Vec<usize> {
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
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval<usize>>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(
 intervals: Vec<Interval<usize>>, lines: Vec<String>, line_number: bool, ) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { if line_number { print!("{}: ", line_no + 1); } println!("{}", line); } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   #[derive(Parser)] #[command(version, about, long_about = None)] struct Cli {
 /// Prefix each line of output with the 1-based line number within its /// input file. #[arg(short, long, default_value_t = false)] line_number: bool,   /// Print num lines of trailing context before matching lines. #[arg(short, long, default_value_t = 0, value_name = "num")] before_context: u8,   /// Print num lines of trailing context after matching lines. #[arg(short, long, default_value_t = 0, value_name = "num")] after_context: u8,   /// The regular expression to match. #[arg(required = true)] pattern: String,   /// List of files to search. #[arg(required = true)] files: Vec<PathBuf>, } 
// Result from a thread
struct RustleSuccess {
    intervals: Vec<Interval<usize>>,
    lines: Vec<String>,
}

// Result from a failed thread
struct RustleFailure {
    error: String,
}

fn main() {
    // let cli = Cli::parse(); // for production use
    // mock command line arguments
    let cli = match Cli::try_parse_from([
        "rustle", // executable name
        "--line-number",
        "--before-context",
        "1",
        "--after-context",
        "1",
        "(all)|(will)", // pattern
        // file(s)...
        "poem.txt",
        "bad_file.txt", // intention failure
        "scoped_threads.txt",
    ]) {
        Ok(cli) => cli,
        Err(e) => {
            eprintln!("Error parsing command line arguments: {e:?}");
            exit(1);
        }
    };

    // map of filename/file contents to simulate opening a file
    let mock_disk = HashMap::from([
        (
            "poem.txt",
            "I have a little shadow that goes in and out with me,
And what can be the use of him is more than I can see.
He is very, very like me from the heels up to the head;
And I see him jump before me, when I jump into my bed.

The funniest thing about him is the way he likes to grow -
Not at all like proper children, which is always very slow;
For he sometimes shoots up taller like an india-rubber ball,
And he sometimes gets so little that there's none of him at all.",
        ),
        (
            "scoped_threads.txt",
            "When we work with scoped threads, the compiler can clearly see,
if the variables we want to use will be available to me.
Because of this visibility, I'm runtime error free!
And issues in my code will be exposed by rustc.
If this sort of safety is provided at native speeds,
there's simply no compelling case to stick with cpp!",
        ),
    ]);

    // get values from clap
 let pattern = cli.pattern; let line_number = cli.line_number; let before_context = cli.before_context as usize; let after_context = cli.after_context as usize;    let files = cli.files;
  // compile the regular expression let regex = match Regex::new(&pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } }; 
    thread::scope(|s| {
        let handles: Vec<_> = files
            .iter()
            .map(|file| {
                let filename = match file.to_str() {
                    Some(filename) => filename,
                    None => {
                        return Err(RustleFailure {
                            error: format!(
                                "Invalid filename: {}",
                                file.display()
                            ),
                        })
                    }
                };

                // attempt to open the file
                //let lines = match File::open(filename) {
                //    // convert the poem into lines
                //    Ok(file) => read_file(file),
                //    Err(e) => {
                //        eprintln!("Error opening {filename}: {e}");
                //        exit(1);
                //    }
                //};

                if !mock_disk.contains_key(filename) {
                    return Err(RustleFailure {
                        error: format!("File not found: {}", filename),
                    });
                }

                Ok(filename)
            })
            .map_ok(|filename| {
                // only spawn a thread for accessible file
                s.spawn(|| {
                    let contents = mock_disk.get(filename).unwrap();
                    let mock_file = std::io::Cursor::new(contents);
                    let lines = read_file(mock_file);

                    // store the 0-based line number for any matched line
                    let match_lines = find_matching_lines(&lines, &regex);

                    // create intervals of the form [a,b] with the before/after
                    // context
                    let intervals = match create_intervals(
                        match_lines,
                        before_context,
                        after_context,
                    ) {
                        Ok(intervals) => intervals,
                        Err(_) => return Err(RustleFailure {
                            error: String::from(
                                "An error occurred while creating intervals",
                            ),
                        }),
                    };

                    // merge overlapping intervals
                    let intervals = merge_intervals(intervals);
                    Ok(RustleSuccess { intervals, lines })
                })
            })
            .collect();

        // process all the results
        for handle in handles {
            let result = match handle {
                Ok(scoped_join_handle) => scoped_join_handle,
                Err(e) => {
                    eprintln!("{}", e.error);
                    continue;
                }
            };

            if let Ok(result) = result.join() {
                match result {
                    Ok(result) => print_results(
                        result.intervals,
                        result.lines,
                        line_number,
                    ),
                    Err(e) => eprintln!("{}", e.error),
                };
            };
        }
    });
}
  pub mod interval {
 /// A list specifying general categories of Interval errors. #[derive(Debug)] pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ #[derive(Debug, PartialEq)] pub struct Interval<T> { pub start: T, pub end: T, }   impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } }   use std::fmt; impl<T: fmt::Display> fmt::Display for Interval<T> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result { write!(f, "[{}, {}]", self.start, self.end) } }   use std::cmp::Ordering; impl<T: PartialEq + PartialOrd> PartialOrd for Interval<T> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { if self == other { Some(Ordering::Equal) } else if self.end < other.start { Some(Ordering::Less) } else if self.start > other.end { Some(Ordering::Greater) } else { None // Intervals overlap } } } }
```

> 缺少错误输出
> 
> ```rs
> File not found: bad_file.txt 
> ```
> 
> 坏文件的错误消息没有出现在 playground 输出中，因为标准错误输出没有被捕获。

我们现在的 rustle 程序是多线程的，并并行处理所有输入文件！让我们回顾一下代码更改。

### `mock_disk`

`mock_disk` [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html) 模拟磁盘访问以检查文件是否存在并可访问。文件名作为键，而文件内容作为值。这种方法有助于测试和开发，但在这里的使用仅限于与 Rust playground 兼容。为了确保创建多个线程，我添加了一首由“我”本人创作的诗。

### `thread::scope`

1.  使用 `map` 迭代器适配器遍历命令行上指定的所有文件，该适配器返回一个 `Result`。`Ok` 变体包含有效的文件名，而 `Error` 变体包含无效文件名的错误。

1.  `map_ok` 迭代器适配器处理每个 `Result`，对任何 `Ok` 值调用提供的闭包，使我们能够忽略任何无效的文件名。提供的 `Scope` (`s`) 为每个文件生成一个线程以进行处理。闭包返回一个 `Result`：如果处理失败，则返回包含错误消息的 `RustleFailure` 结构体的 `Err`，如果成功，则返回包含输入文件中的区间和行的 `RustleSuccess` 结构体的 `Ok`。

1.  使用 `collect` 从每个文件迭代创建结果向量（`Vec`），并将其绑定到 `handles`。

1.  最后，使用 for 循环遍历 `handles` 向量中的元素。将任何错误打印到标准错误，并将成功的模式匹配结果传递给 `print_results` 函数以输出到标准输出。

### `find_matching_lines`

由于每个线程都需要访问 `regex` 对象，因此值是借用而不是移动。

# 总结

+   所有权和类型系统是管理内存安全和并发问题的强大工具。通过利用所有权和类型检查，Rust 中的许多并发错误在编译时而不是在运行时被捕获。

+   与非作用域线程不同，作用域线程可以借用非 `'static` 数据，因为作用域确保在它结束之前所有线程都已连接。

# 练习

实现的 fork/join 模型是次优的，因为它在打印任何结果之前等待所有线程完成并加入。为了解决这个问题，我们可以使用`mpsc`（多个生产者，单个消费者）模块，它允许线程在准备好结果后立即将结果发送到中央接收器。这使得程序能够立即开始输出结果，提高了其响应性和效率。修改程序以使用`mpsc`。

**提示**：最终解决方案的结构应类似于：

```rs
fn main() {
    // create the mpsc channel
    let (tx, rx) = channel::<Result<RustleSuccess, RustleFailure>>();

    // create a non-scoped thread for processing incoming messages
    let handle = thread::spawn(move || {
        // process results as they arrive
    });

    // create scoped threads for file processing
    thread::scope(|s| {
        // spawn threads and do work
        // send result to the channel
    });

    // drop the last sender to stop rx from waiting for messages
    drop(tx);

    // prevent main from returning until all results are processed
    let _ = handle.join();
}
```

```rs
#![allow(unused_imports)]
use clap::Parser;
use interval::{Interval, IntervalError};
use itertools::Itertools;
use regex::Regex;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process::exit;
use std::thread;

fn find_matching_lines(lines: &[String], regex: &Regex) -> Vec<usize> {
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
) -> Result<Vec<Interval<usize>>, IntervalError> {
    lines
        .iter()
        .map(|line| {
            let start = line.saturating_sub(before_context);
            let end = line.saturating_add(after_context);
            Interval::new(start, end)
        })
        .collect()
}

fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
    // merge overlapping intervals
    intervals
        .into_iter()
        .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c)))
        .collect()
}

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
    BufReader::new(file).lines().map_while(Result::ok).collect()
}

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

// Result from a thread
struct RustleSuccess {
    intervals: Vec<Interval<usize>>,
    lines: Vec<String>,
}

// Result from a failed thread
struct RustleFailure {
    error: String,
}

fn main() {
    // let cli = Cli::parse(); // for production use
    // mock command line arguments
    let cli = match Cli::try_parse_from([
        "rustle", // executable name
        "--line-number",
        "--before-context",
        "1",
        "--after-context",
        "1",
        "(all)|(will)", // pattern
        // file(s)...
        "poem.txt",
        "bad_file.txt", // intention failure
        "scoped_threads.txt",
    ]) {
        Ok(cli) => cli,
        Err(e) => {
            eprintln!("Error parsing command line arguments: {e:?}");
            exit(1);
        }
    };

    // map of filename/file contents to simulate opening a file
    let mock_disk = HashMap::from([
        (
            "poem.txt",
            "I have a little shadow that goes in and out with me,
And what can be the use of him is more than I can see.
He is very, very like me from the heels up to the head;
And I see him jump before me, when I jump into my bed.

The funniest thing about him is the way he likes to grow -
Not at all like proper children, which is always very slow;
For he sometimes shoots up taller like an india-rubber ball,
And he sometimes gets so little that there's none of him at all.",
        ),
        (
            "scoped_threads.txt",
            "When we work with scoped threads, the compiler can clearly see,
if the variables we want to use will be available to me.
Because of this visibility, I'm runtime error free!
And issues in my code will be exposed by rustc.
If this sort of safety is provided at native speeds,
there's simply no compelling case to stick with cpp!",
        ),
    ]);

    // get values from clap
    let pattern = cli.pattern;
    let line_number = cli.line_number;
    let before_context = cli.before_context as usize;
    let after_context = cli.after_context as usize;
    let files = cli.files;

    // compile the regular expression
    let regex = match Regex::new(&pattern) {
        Ok(re) => re, // bind re to regex
        Err(e) => {
            eprintln!("{e}"); // write to standard error
            exit(1);
        }
    };

    thread::scope(|s| {
        let handles: Vec<_> = files
            .iter()
            .map(|file| {
                let filename = match file.to_str() {
                    Some(filename) => filename,
                    None => {
                        return Err(RustleFailure {
                            error: format!(
                                "Invalid filename: {}",
                                file.display()
                            ),
                        })
                    }
                };

                // attempt to open the file
                //let lines = match File::open(filename) {
                //    // convert the poem into lines
                //    Ok(file) => read_file(file),
                //    Err(e) => {
                //        eprintln!("Error opening {filename}: {e}");
                //        exit(1);
                //    }
                //};

                if !mock_disk.contains_key(filename) {
                    return Err(RustleFailure {
                        error: format!("File not found: {}", filename),
                    });
                }

                Ok(filename)
            })
            .map_ok(|filename| {
                // only spawn a thread for accessible file
                s.spawn(|| {
                    let contents = mock_disk.get(filename).unwrap();
                    let mock_file = std::io::Cursor::new(contents);
                    let lines = read_file(mock_file);

                    // store the 0-based line number for any matched line
                    let match_lines = find_matching_lines(&lines, &regex);

                    // create intervals of the form [a,b] with the before/after
                    // context
                    let intervals = match create_intervals(
                        match_lines,
                        before_context,
                        after_context,
                    ) {
                        Ok(intervals) => intervals,
                        Err(_) => return Err(RustleFailure {
                            error: String::from(
                                "An error occurred while creating intervals",
                            ),
                        }),
                    };

                    // merge overlapping intervals
                    let intervals = merge_intervals(intervals);
                    Ok(RustleSuccess { intervals, lines })
                })
            })
            .collect();

        // process all the results
        for handle in handles {
            let result = match handle {
                Ok(scoped_join_handle) => scoped_join_handle,
                Err(e) => {
                    eprintln!("{}", e.error);
                    continue;
                }
            };

            if let Ok(result) = result.join() {
                match result {
                    Ok(result) => print_results(
                        result.intervals,
                        result.lines,
                        line_number,
                    ),
                    Err(e) => eprintln!("{}", e.error),
                };
            };
        }
    });
}

pub mod interval {
    /// A list specifying general categories of Interval errors.
    #[derive(Debug)]
    pub enum IntervalError {
        /// Start is not less than or equal to end
        StartEndRangeInvalid,
        /// Two intervals to be merged do not overlap
        NonOverlappingInterval,
    }

    /// A closed-interval [`start`, `end`] type used for representing a range of
    /// values between `start` and `end` inclusively.
    ///
    /// # Examples
    ///
    /// You can create an `Interval` using `new`.
    ///
    /// ~~~rs
    /// let interval = Interval::new(1, 10).unwrap();
    /// assert_eq!(interval.start, 1);
    /// assert_eq!(interval.end, 10);
    /// ~~~
    #[derive(Debug, PartialEq)]
    pub struct Interval<T> {
        pub start: T,
        pub end: T,
    }

    impl<T: Copy + PartialOrd> Interval<T> {
        /// Creates a new `Interval` set to `start` and `end`.
        ///
        /// # Examples
        ///
        /// ~~~rs
        /// let interval = Interval::new(1, 10).unwrap();
        /// assert_eq!(interval.start, 1);
        /// assert_eq!(interval.end, 10);
        /// ~~~
        pub fn new(start: T, end: T) -> Result<Self, IntervalError> {
            if start <= end {
                Ok(Self { start, end })
            } else {
                Err(IntervalError::StartEndRangeInvalid)
            }
        }

        /// Checks if two intervals overlap. Overlapping intervals have at
        /// least one point in common.
        ///
        /// # Examples
        ///
        /// ~~~rs
        /// let a = Interval::new(1, 3).unwrap();
        /// let b = Interval::new(3, 5).unwrap();
        /// assert_eq!(a.overlaps(&b), true);
        /// assert_eq!(b.overlaps(&a), true);
        /// ~~~
        ///
        /// ~~~rs
        /// let a = Interval::new(1, 5).unwrap();
        /// let b = Interval::new(2, 4).unwrap();
        /// assert_eq!(a.overlaps(&b), true);
        /// assert_eq!(b.overlaps(&a), true);
        /// ~~~
        ///
        /// ~~~rs
        /// let a = Interval::new(1, 3).unwrap();
        /// let b = Interval::new(4, 6).unwrap();
        /// assert_eq!(a.overlaps(&b), false);
        /// assert_eq!(b.overlaps(&a), true);
        /// ~~~
        pub fn overlaps(&self, other: &Interval<T>) -> bool {
            self.end >= other.start
        }

        /// Merges two intervals returning a new `Interval`.
        ///
        /// The merged `Interval` range includes the union of ranges from each
        /// `Interval`.
        ///
        /// # Examples
        ///
        /// ~~~rs
        /// let a = Interval::new(1, 3).unwrap();
        /// let b = Interval::new(3, 5).unwrap();
        /// let c = a.merge(&b).unwrap();
        /// assert_eq!(c.start, 1);
        /// assert_eq!(c.end, 5);
        /// ~~~
        pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
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

    use std::fmt;
    impl<T: fmt::Display> fmt::Display for Interval<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "[{}, {}]", self.start, self.end)
        }
    }

    use std::cmp::Ordering;
    impl<T: PartialEq + PartialOrd> PartialOrd for Interval<T> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            if self == other {
                Some(Ordering::Equal)
            } else if self.end < other.start {
                Some(Ordering::Less)
            } else if self.start > other.end {
                Some(Ordering::Greater)
            } else {
                None // Intervals overlap
            }
        }
    }
}
```

<details><summary>解决方案</summary>

```rs
#![allow(unused_imports)] use clap::Parser; use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::collections::HashMap; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::path::PathBuf; use std::process::exit; use std::sync::mpsc::channel;
use std::thread;   fn find_matching_lines(lines: &[String], regex: &Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval<usize>>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(
 intervals: Vec<Interval<usize>>, lines: Vec<String>, line_number: bool, ) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { if line_number { print!("{}: ", line_no + 1); } println!("{}", line); } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   #[derive(Parser)] #[command(version, about, long_about = None)] struct Cli {
 /// Prefix each line of output with the 1-based line number within its /// input file. #[arg(short, long, default_value_t = false)] line_number: bool,   /// Print num lines of trailing context before matching lines. #[arg(short, long, default_value_t = 0, value_name = "num")] before_context: u8,   /// Print num lines of trailing context after matching lines. #[arg(short, long, default_value_t = 0, value_name = "num")] after_context: u8,   /// The regular expression to match. #[arg(required = true)] pattern: String,   /// List of files to search. #[arg(required = true)] files: Vec<PathBuf>, }   // Result from a thread struct RustleSuccess {
 intervals: Vec<Interval<usize>>, lines: Vec<String>, }   // Result from a failed thread struct RustleFailure {
 error: String, } 
fn main() {
 // let cli = Cli::parse(); // for production use // mock command line arguments let cli = match Cli::try_parse_from([ "rustle", // executable name "--line-number", "--before-context", "1", "--after-context", "1", "(all)|(will)", // pattern // file(s)... "poem.txt", "bad_file.txt", // intention failure "scoped_threads.txt", ]) { Ok(cli) => cli, Err(e) => { eprintln!("Error parsing command line arguments: {e:?}"); exit(1); } };   // map of filename/file contents to simulate opening a file let mock_disk = HashMap::from([ ( "poem.txt", "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.",
 ), ( "scoped_threads.txt", "When we work with scoped threads, the compiler can clearly see, if the variables we want to use will be available to me. Because of this visibility, I'm runtime error free! And issues in my code will be exposed by rustc. If this sort of safety is provided at native speeds, there's simply no compelling case to stick with cpp!",
 ), ]);   // get values from clap let pattern = cli.pattern; let line_number = cli.line_number; let before_context = cli.before_context as usize; let after_context = cli.after_context as usize; let files = cli.files;   // compile the regular expression let regex = match Regex::new(&pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };      // create the mpsc channel
    let (tx, rx) = channel::<Result<RustleSuccess, RustleFailure>>();

    // create a non-scoped thread for processing incoming messages
    let handle = thread::spawn(move || {
        // process all the results
        while let Ok(result) = rx.recv() {
            match result {
                Ok(result) => {
                    print_results(result.intervals, result.lines, line_number)
                }
                Err(e) => eprintln!("{}", e.error),
            };
        }
    });

    thread::scope(|s| {
        for file in &files {
            s.spawn(|| {
                // check if valid filename
                let filename = match file.to_str() {
                    Some(filename) => filename,
                    None => {
                        return tx.send(Err(RustleFailure {
                            error: format!(
                                "Invalid filename: {}",
                                file.display()
                            ),
                        }))
                    }
                };

                // attempt to open the file
 //let handle = match File::open(filename) { //    Ok(handle) => handle, //    Err(e) => { //        return tx.send(Err(RustleFailure { //            error: format!("Error opening {filename}: {e}"), //        })) //    } //};                if !mock_disk.contains_key(filename) {
                    return tx.send(Err(RustleFailure {
                        error: format!("File not found: {}", filename),
                    }));
                }

                // process a file
                let contents = mock_disk.get(filename).unwrap();
                let mock_file = std::io::Cursor::new(contents);
                let lines = read_file(mock_file);

                // store the 0-based line number for any matched line
                let match_lines = find_matching_lines(&lines, &regex);

                // create intervals of the form [a,b] with the before/after context
                let intervals =
                    match create_intervals(
                        match_lines,
                        before_context,
                        after_context,
                    ) {
                        Ok(intervals) => intervals,
                        Err(_) => return tx.send(Err(RustleFailure {
                            error: String::from(
                                "An error occurred while creating intervals",
                            ),
                        })),
                    };

                // merge overlapping intervals
                let intervals = merge_intervals(intervals);
                tx.send(Ok(RustleSuccess { intervals, lines }))
            });
        }
    });

    // drop the last sender to stop rx from waiting for messages
    drop(tx);

    // prevent main from returning until all results are processed
    let _ = handle.join();
}
  pub mod interval {
 /// A list specifying general categories of Interval errors. #[derive(Debug)] pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ #[derive(Debug, PartialEq)] pub struct Interval<T> { pub start: T, pub end: T, }   impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at /// least one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } }   use std::fmt; impl<T: fmt::Display> fmt::Display for Interval<T> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result { write!(f, "[{}, {}]", self.start, self.end) } }   use std::cmp::Ordering; impl<T: PartialEq + PartialOrd> PartialOrd for Interval<T> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { if self == other { Some(Ordering::Equal) } else if self.end < other.start { Some(Ordering::Less) } else if self.start > other.end { Some(Ordering::Greater) } else { None // Intervals overlap } } } }
```</details>

# 下一页

总结一下！
