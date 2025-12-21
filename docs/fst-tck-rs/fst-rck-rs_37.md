# 作用域和隐私

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/scope_and_privacy.html`](https://freddiehaddad.github.io/fast-track-to-rust/scope_and_privacy.html)

我们将把所有与`Interval`相关的代码转换为模块。要定义一个模块，我们使用`mod`关键字后跟模块的名称，并在花括号内封装模块体。

```rs
mod interval {
    // module body
}
```

这是我们的 rustle 程序的新版本，其中与`Interval`相关的部分已移动到`interval`模块内部。此外，模块中已添加注释，这些注释将在即将到来的部分中用于生成文档。运行代码看看效果吧！

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   mod interval {
    /// A list specifying general categories of Interval errors.
    enum IntervalError {
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
    struct Interval {
        start: usize,
        end: usize,
    }

    impl Interval {
        /// Creates a new `Interval` set to `start` and `end`.
        ///
        /// # Examples
        ///
        /// ~~~rs
        /// let interval = Interval::new(1, 10).unwrap();
        /// assert_eq!(interval.start, 1);
        /// assert_eq!(interval.end, 10);
        /// ~~~
        fn new(start: usize, end: usize) -> Result<Self, IntervalError> {
            if start <= end {
                Ok(Self { start, end })
            } else {
                Err(IntervalError::StartEndRangeInvalid)
            }
        }

        /// Checks if two intervals overlap. Overlapping intervals have at least
        /// one point in common.
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
        fn overlaps(&self, other: &Interval) -> bool {
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
}
```

哎呀！看起来我们有很多编译器错误！在混乱中，有两个与作用域和隐私有关的错误。

+   [E0412](https://doc.rust-lang.org/stable/error_codes/E0412.html)：在此作用域中找不到类型`Interval`

+   [E0433](https://doc.rust-lang.org/stable/error_codes/E0433.html)：无法解析：使用未声明的类型`Interval`

> 记住，你总是可以使用`rustc --explain EXXXX`来获取错误消息的详细解释。

## 作用域

第一个错误表明`Interval`类型不在作用域内。这是因为它现在是`interval`模块的一部分。要访问它，我们可以使用完整的路径名`interval::Interval`或使用`use`创建快捷方式。由于我们不希望在代码中替换每个`Interval`的出现，我们将利用`use`。此外，我们需要访问`IntervalError`，所以我们将同时将其引入作用域。在引入多个类型到作用域时，我们可以将它们包裹在`{}`中，并用逗号分隔。

在这个更改到位后，再次运行代码。

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError};
use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   mod interval {
 /// A list specifying general categories of Interval errors. enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ struct Interval { start: usize, end: usize, }   impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ fn new(start: usize, end: usize) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ fn overlaps(&self, other: &Interval) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

糟糕！更多编译器错误！

## 隐私

在我们定义`interval`模块之前，所有类型及其方法都是公共的。然而，一旦我们将所有内容封装在模块中，它们就变成了私有的！默认情况下，模块内的代码对其父模块是私有的。要使模块公开，我们需要使用`pub mod`来声明它，而不是仅仅使用`mod`。让我们添加`pub`前缀并再次运行程序。

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ struct Interval { start: usize, end: usize, }   impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ fn new(start: usize, end: usize) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ fn overlaps(&self, other: &Interval) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

更多编译器错误！谁能想到创建一个模块会这么复杂？这一系列错误的原因是帮助我们理解模块的作用域和隐私。出现的模式是模块默认将所有内容设置为私有。仅仅声明模块为公共是不够的；模块内的每个类型和方法都必须显式声明为公共，如果这是预期的设计。所以，让我们在方法和类型前加上`pub`前缀，并希望成功编译！

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors.    pub enum IntervalError {
 /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~    pub struct Interval {
 start: usize, end: usize, }   impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~        pub fn new(start: usize, end: usize) -> Result<Self, IntervalError> {
 if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~        pub fn overlaps(&self, other: &Interval) -> bool {
 self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~        pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
 if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

好吧，上一次，我保证！最后关于隐私的笔记，正如编译器错误所指出的，`struct`的字段默认是私有的。所以，最后一步是将字段公开。让我们这样做，并最终成功编译。祝我们好运！

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub struct Interval {        pub start: usize,
        pub end: usize,
 }   impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: usize, end: usize) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

最后，代码编译成功了！现在，你可能想知道为什么我们不需要将 `enum` 变体声明为公开。如果你这么想，那是个很好的发现！原因是存在两个例外于 Rust 的 *一切默认为私有*^(1) 行为：

1.  在 `pub` Trait 中的关联项默认是公开的。

1.  在 `pub enum` 中的 `enum` 变体默认是公开的。

# 摘要

本节重点强调了 Rust 在模块方面的 *一切默认为私有* 的行为。在开发软件时，利用隐私优势，并仔细决定 API 的哪些部分应该公开。

Rust 在项目管理方面非常详细。当你创建自己的模块和 crate 时，回顾 [使用包、crate 和模块管理增长项目](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) 这一部分将非常有价值。

# 练习

> 这些练习必须在本地完成。

+   将 `interval` 模块从 `main.rs` 移出，放入一个单独的文件中。探索两种方法：

    1.  首先，在 `src` 目录下创建一个名为 `interval.rs` 的文件。

    1.  接下来，在 `src` 目录下创建一个名为 `interval` 的目录，并将 `interval.rs` 移动到其中。

+   **高级**: 创建外部 crate

    1.  创建一个名为 `interval` 的库 crate，使用 `cargo new --lib interval` 命令，并将区间代码移动到其中。

    1.  如果你还没有创建，请创建一个名为 `rustle` 的二进制 crate，并更新 `Cargo.toml` 文件以使用上一步骤中的外部 crate。有关指导，请参阅 [The Cargo Book](https://doc.rust-lang.org/cargo/) 中的 [指定依赖项](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) 部分。

# 下一步

现在，让我们深入了解泛型类型，并使我们的 `Interval` 泛型化！

* * *

1.  有关详细信息，请参阅 [可见性和隐私](https://doc.rust-lang.org/reference/visibility-and-privacy.html) 参考。↩
