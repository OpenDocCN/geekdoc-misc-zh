# 区间

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/interval.html`](https://freddiehaddad.github.io/fast-track-to-rust/interval.html)

我们当前版本的`Interval`仅限于`usize`类型。如果我们想支持浮点值、负整数或其他奇特的数值类型，它将不起作用。我们将通过使其与任何数值类型兼容来解决此问题，但有一些限制.^(1)

## 泛型数据类型

我们当前`Interval` `struct`的定义指定了字段类型为`usize`。为了重新定义`struct`以使用其字段的泛型类型参数，我们使用`<>`语法。

```rs
pub struct Interval<T> {
    pub start: T,
    pub end: T,
}
```

> 通过使用单个泛型类型来定义`Interval<T>`，我们表明`Interval<T>` `struct`是泛型类型`T`的，并且字段`start`和`end`都是同一类型，无论它是什么。如果我们尝试使用不同类型的字段创建`Interval<T>`的实例，我们的代码将无法编译。为了支持不同类型的字段，我们需要指定额外的泛型类型，例如`struct Interval<T, U>`。

你可能已经猜到了，但这段代码无法编译。花点时间想想为什么可能会这样，然后运行代码看看编译器有什么要说的。

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval>) -> Vec<Interval> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~    pub struct Interval<T> {
        pub start: T,
        pub end: T,
    }
  impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: usize, end: usize) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

如你所料，有很多编译器错误，而且它们非常有帮助！

+   [E0107](https://doc.rust-lang.org/stable/error_codes/E0107.html): `struct` `Interval`缺少泛型

让我们逐个分析错误。第一个错误告诉我们，第 26 行的返回值引用了一个泛型类型，但没有指定它。它显示了第 141 行的类型定义，并提供了如何纠正它的有用提示。编译器建议将`<T>`附加到`Interval`并指定`T`的类型，在我们的情况下将是`usize`。

```rs
error[E0107]: missing generics for struct `Interval`
   --> src/main.rs:26:17
    |
26  | ) -> Result<Vec<Interval>, IntervalError> {
    |                 ^^^^^^^^ expected 1 generic argument
    |
note: struct defined here, with 1 generic parameter: `T`
   --> src/main.rs:141:16
    |
141 |     pub struct Interval<T> {
    |                ^^^^^^^^ -
help: add missing generic argument
    |
26  | ) -> Result<Vec<Interval<T>>, IntervalError> {
    |                         +++ 
```

修复方法应该相对容易理解，因为我们已经为其他我们处理过的泛型类型使用了相同的方法。让我们将修复应用到所有函数并再次尝试！

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
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

fn print_results(intervals: Vec<Interval<usize>>, lines: Vec<String>) {
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
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub struct Interval<T> { pub start: T, pub end: T, }   impl Interval { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: usize, end: usize) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

如预期的那样，我们还有一些编译器错误需要解决，这些错误引导我们了解了如何为泛型类型实现方法！

```rs
error[E0107]: missing generics for struct `Interval`
   --> src/main.rs:146:10
    |
146 |     impl Interval {
    |          ^^^^^^^^ expected 1 generic argument
    |
note: struct defined here, with 1 generic parameter: `T`
   --> src/main.rs:141:16
    |
141 |     pub struct Interval<T> {
    |                ^^^^^^^^ -
help: add missing generic argument
    |
146 |     impl Interval<T> {
    |                  +++

error[E0107]: missing generics for struct `Interval`
   --> src/main.rs:189:40
    |
189 |         pub fn overlaps(&self, other: &Interval) -> bool {
    |                                        ^^^^^^^^ expected 1 generic argument
    |
note: struct defined here, with 1 generic parameter: `T`
   --> src/main.rs:141:16
    |
141 |     pub struct Interval<T> {
    |                ^^^^^^^^ -
help: add missing generic argument
    |
189 |         pub fn overlaps(&self, other: &Interval<T>) -> bool {
    |                                                +++

For more information about this error, try `rustc --explain E0107`. 
```

## 固有实现

我们定义了两种主要的实现类型：固有实现（独立）和特性实现.^(2) 我们将首先关注固有实现，并在本节末尾探讨特性实现。

我们需要更新我们的`impl`块以支持泛型类型参数，其语法如下：

```rs
impl<T> Type<T> {}  // Type is replaced with Interval for our case
```

这里是必要的更改。请审查它们，然后再次运行程序。

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval<usize>>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval<usize>>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub struct Interval<T> { pub start: T, pub end: T, }      impl<T> Interval<T> {
 /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~        pub fn new(start: T, end: T) -> Result<Self, IntervalError> {
            if start <= end {
                Ok(Self { start, end })
            } else {
                Err(IntervalError::StartEndRangeInvalid)
            }
        }

 /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~        pub fn overlaps(&self, other: &Interval<T>) -> bool {
            self.end >= other.start
        }
  /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

嗯，这没有起作用！现在我们有两个新的编译器错误：

+   [E0369]: 二元运算符`<=`不能应用于类型`T`

+   [E0507]: 无法从共享引用后面的`self.start`移动

这没关系，因为这些错误完美地过渡到了特性边界！

## 特性边界

编译器生成了一些非常有用的错误信息，我们可以将其分为两类，这两类都建议使用特质界限：

```rs
error[E0369]: binary operation `<=` cannot be applied to type `T`
   --> src/main.rs:157:22
    |
157 |             if start <= end {
    |                ----- ^^ --- T
    |                |
    |                T
    |
help: consider restricting type parameter `T`
    |
146 |     impl<T: std::cmp::PartialOrd> Interval<T> {
    |           ++++++++++++++++++++++

error[E0507]: cannot move out of `self.start` which is behind a shared reference
   --> src/main.rs:210:28
    |
210 |                     start: self.start,
    |                            ^^^^^^^^^^ move occurs because `self.start` has
                                            type `T`, which does not implement the
                                            `Copy` trait
    |
help: if `T` implemented `Clone`, you could clone the value
   --> src/main.rs:146:10
    |
146 |     impl<T> Interval<T> {
    |          ^ consider constraining this type parameter with `Clone`
...
210 |                     start: self.start,
    |                            ---------- you could clone this value 
```

在介绍了特质界限之后，一切都将变得清晰。让我们从第一个错误开始。编译器指示在 `new` 函数中尝试对两个泛型类型进行比较，而并非所有类型都支持这种能力。换句话说，并非所有类型都实现了 `PartialOrd` 特质，这是使用比较运算符如 `<=` 和 `>=` 所必需的。

> 对于有面向对象编程背景的人来说，可以将特质（trait）视为与接口（interface）类似。

```rs
pub fn new(start: T, end: T) -> Result<Self, IntervalError> {
    if start <= end {
        Ok(Self { start, end })
    } else {
        Err(IntervalError::StartEndRangeInvalid)
    }
}
```

由于我们的 `Interval` `struct` 是泛型 `T` 的，因此 `start` 和 `end` 的类型可以是任何类型，包括不可比较的类型。因此，编译器指示我们将 `T` 限制为任何实现了 `PartialOrd` 特质的类型。换句话说，我们需要对 `T` 设置一个 *限制*。

下一个错误需要我们重新审视 Rust 中的移动语义（move semantics）问题。除了原始类型外，大多数标准库类型以及第三方 crate 中的类型都没有实现 `Copy` 特质。换句话说，它们没有 *复制语义*。让我们检查出现错误的函数：

```rs
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
```

`merge` 函数借用 `self` 和 `other` 的值。如果两个区间重叠，则返回一个新的区间，并将值复制到其中。由于我们一直在使用 `usize` 类型，这是一个实现了 `Copy` 特质的类型，所以这可以工作。为了确保它继续工作，我们需要对 `T` 设置另一个限制，限制它为实现了 `Copy` 特质的类型。

> 编译器还提到了 `Clone` 特质，该特质允许通过 `clone` 方法显式地复制一个对象。这意味着我们可以将特质界限指定为 `Clone` 而不是 `Copy`，并更新方法以显式调用 `clone`。

在理解了特质界限之后，让我们来看看如何将这些建限应用于我们的 `Interval`。现在程序工作了吗？

```rs
#![allow(unused_imports)] extern crate regex; // this is needed for the playground use interval::{Interval, IntervalError}; use itertools::Itertools; use regex::Regex; use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit;   fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
 lines .iter() .enumerate() .filter_map(|(i, line)| match regex.is_match(line) { true => Some(i), false => None, }) .collect() // turns anything iterable into a collection }   fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Result<Vec<Interval<usize>>, IntervalError> {
 lines .iter() .map(|line| { let start = line.saturating_sub(before_context); let end = line.saturating_add(after_context); Interval::new(start, end) }) .collect() }   fn merge_intervals(intervals: Vec<Interval<usize>>) -> Vec<Interval<usize>> {
 // merge overlapping intervals intervals .into_iter() .coalesce(|p, c| p.merge(&c).map_err(|_| (p, c))) .collect() }   fn print_results(intervals: Vec<Interval<usize>>, lines: Vec<String>) {
 for interval in intervals { for (line_no, line) in lines .iter() .enumerate() .take(interval.end + 1) .skip(interval.start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};   // compile the regular expression let regex = match Regex::new(pattern) { Ok(re) => re, // bind re to regex Err(e) => { eprintln!("{e}"); // write to standard error exit(1); } };   // store the 0-based line number for any matched line let match_lines = find_matching_lines(&lines, regex);   // create intervals of the form [a,b] with the before/after context let intervals = match create_intervals(match_lines, before_context, after_context) { Ok(intervals) => intervals, Err(_) => { eprintln!("An error occurred while creating intervals"); exit(1); } };   // merge overlapping intervals let intervals = merge_intervals(intervals);   // print the lines print_results(intervals, lines); }   pub mod interval {
 /// A list specifying general categories of Interval errors. pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub struct Interval<T> { pub start: T, pub end: T, }      impl<T: Copy + PartialOrd> Interval<T> {
 /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
```

哇！现在我们有一个通用的 `Interval` 模块，它可以支持任何实现了 `Copy` 和 `PartialOrd` 特质的类型！

# 练习

+   将程序修改为使用 `Clone` 特质而不是 `Copy` 特质。

<details><summary>解决方案</summary>

```rs
impl<T: Clone + PartialOrd> Interval<T> {
    pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> {
        if self.overlaps(other) {
            Ok(Self {
                start: self.start.clone(),
                end: other.end.clone(),
            })
        } else {
            Err(IntervalError::NonOverlappingInterval)
        }
    }
}
```</details>

```rs
#![allow(unused_imports)]
extern crate regex; // this is needed for the playground
use interval::{Interval, IntervalError};
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

fn print_results(intervals: Vec<Interval<usize>>, lines: Vec<String>) {
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

pub mod interval {
    /// A list specifying general categories of Interval errors.
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
}
```

# 下一步

让我们更深入地探讨特质！

* * *

1.  我们对支持类型施加的限制称为 [特质界限](https://doc.rust-lang.org/reference/trait-bounds.html)。↩

1.  有关 `impl Trait` 语法的信息，请参阅 [Rust 书籍](https://doc.rust-lang.org/book/ch10-02-traits.html#returning-types-that-implement-traits) ↩
