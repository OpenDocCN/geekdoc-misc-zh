# 特性

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/traits.html`](https://freddiehaddad.github.io/fast-track-to-rust/traits.html)

在上一节中，我们指定了特性界限来限制可以与我们的`Interval`一起使用的类型。让我们正式化一下什么是特性：

特性正式定义为未知类型`Self`的方法集合：`Self`.^(1)

简单来说，特性允许您以抽象的方式定义共享行为。它指定了一组类型必须实现的方法，类似于其他编程语言中的接口。

《Rust By Example》一书包含了众多[特性](https://doc.rust-lang.org/rust-by-example/trait.html)的示例，并深入探讨了它们的用法。强烈建议复习这些材料。

> 编译器可以使用派生（`#[derive]`）[属性](https://doc.rust-lang.org/reference/attributes.html)自动为某些特性提供基本实现。然而，如果需要更复杂的行为，这些特性仍然可以手动实现。以下是可以派生的特性列表：

+   比较特性：`Eq`([`Eq`](https://doc.rust-lang.org/std/cmp/trait.Eq.html))、`PartialEq`([`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html))、`Ord`、`PartialOrd`([`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html))。

+   [克隆](https://doc.rust-lang.org/std/clone/trait.Clone.html)，通过复制从`&T`创建`T`。

+   [拷贝](https://doc.rust-lang.org/std/marker/trait.Copy.html)，为类型提供*拷贝语义*而不是*移动语义*。

+   [哈希](https://doc.rust-lang.org/std/hash/trait.Hash.html)，从`&T`计算哈希。

+   [默认值](https://doc.rust-lang.org/std/default/trait.Default.html)，创建数据类型的空实例。

+   [调试](https://doc.rust-lang.org/std/fmt/trait.Debug.html)，使用`{:?}`格式化器格式化值。

## 派生特性

使用我们的`Interval`的人可能会发现有一个简单的方法来比较它们很有帮助。例如，用户可能想检查两个区间是否相等。`PartialEq`特性，是`cmp`模块的一部分，指定了任何类型必须定义以实现`PartialEq`特性的两个方法。

```rs
pub trait PartialEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    // Required method
    fn eq(&self, other: &Rhs) -> bool;

    // Provided method
    fn ne(&self, other: &Rhs) -> bool { ... }
}
```

> 注意`ne`方法上面的注释说“提供方法”。这表明如果我们手动实现这个特性，我们只需要为`eq`提供一个实现。

这是我们的修改后的`Interval`，它支持`PartialEq`，归功于派生属性和 Rust 编译器。试试看吧！

> `Debug`特性也已派生，使得区间可以在程序员面向的环境中通过`:?`运算符打印。这种在 Rust 中常见的模式在下面的程序中提供了更有帮助的输出。

```rs
use interval::Interval;

pub mod interval {
 /// A list specifying general categories of Interval errors.    #[derive(Debug)]
    pub enum IntervalError {
 /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, } 
 /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~    #[derive(Debug, PartialEq)]
    pub struct Interval<T> {
 pub start: T, pub end: T, }   impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }

fn main() {
    let a = Interval::new(1, 5).unwrap(); // unwrap returns the Ok value or panics
    let b = Interval::new(1, 5).unwrap();
    let c = Interval::new(2, 4).unwrap();

    // Comparing intervals with eq and ne.
    println!("{:?} == {:?} => {}", a, b, a.eq(&b));
    println!("{:?} == {:?} => {}", a, c, a.eq(&c));
    println!("{:?} != {:?} => {}", a, b, a.ne(&b));
    println!("{:?} != {:?} => {}", a, c, a.ne(&c));

    // Rust supports operator overloading too!
    println!("{:?} == {:?} => {}", a, b, a == b);
    println!("{:?} != {:?} => {}", a, c, a != c);
}
```

> `unwrap()` 方法由 `Result` 和其他类型如 `Option` 实现。对于 `Result`，它返回 `Ok` 值或者在值为 `Err` 时引发恐慌。通常不建议使用 `unwrap()`，这里仅为了简洁而使用。
> 
> 操作符重载
> 
> 你可能已经注意到了使用 `==` 和 `!=` 进行区间比较的区别。这是因为 Rust 支持操作符重载！你可以在 [Rust by Example](https://doc.rust-lang.org/rust-by-example/) 书籍的 [操作符重载](https://doc.rust-lang.org/rust-by-example/trait/ops.html) 部分和 `ops` 模块（[ops](https://doc.rust-lang.org/std/ops/index.html)）中找到所有详细的信息。

## 实现特质

就像比较特质以检查相等性可能很有帮助一样，生成 `Interval` 的用户界面表示也可能很有用。通过实现 `Display` 特质，我们可以非常高效地实现这一点。此外，实现 `Display` 特质还会自动实现 `ToString` 特质，使得可以使用 `to_string()` 方法。让我们增强我们的 `Interval` 代码，以便以 `[x, y]` 的形式打印区间。

下面是 `Display` 特质的定义：

```rs
pub trait Display {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
```

> `Formatter` 旁边的 `<'_>` 后缀被称为 *生命周期注解语法*。^(2)

下面是我们修改后的 `Interval`，实现了 `Display` 特性。试试看吧！

```rs
use interval::Interval;

pub mod interval {
 /// A list specifying general categories of Interval errors. #[derive(Debug)] pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ #[derive(Debug, PartialEq)] pub struct Interval<T> { pub start: T, pub end: T, }      use std::fmt;
    impl<T: fmt::Display> fmt::Display for Interval<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "[{}, {}]", self.start, self.end)
        }
    }
  impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }

fn main() {
    let a = Interval::new(1, 5).unwrap(); // unwrap returns the Ok value or panics
    let b = Interval::new(1, 5).unwrap();
    let b_str = b.to_string();
    let c = Interval::new(2, 4).unwrap();

    println!(
        "Comparisons between three intervals: {}, {}, {}...",
        a, b_str, c
    );

    // Comparing intervals with eq and ne.
    println!("{} == {} => {}", a, b, a.eq(&b));
    println!("{} == {} => {}", a, c, a.eq(&c));
    println!("{} != {} => {}", a, b, a.ne(&b));
    println!("{} != {} => {}", a, c, a.ne(&c));

    // Rust supports operator overloading too!
    println!("{} == {} => {}", a, b, a == b);
    println!("{} != {} => {}", a, c, a != c);
}
```

# 总结

+   我们的区间模块已经增强，支持了几个新功能。

+   我们可以使用 `Debug` 特质打印面向程序员的区间，使用 `Display` 特质打印面向用户的区间。

+   我们对通过 `PartialEq` 和 `PartialOrd` 特质比较区间有限的支持。

+   一个特质以抽象的方式定义了共享行为，指定了一个类型必须实现的方法，类似于其他语言中的接口。

+   编译器可以使用 `#[derive]` 属性自动为某些特质提供基本实现。

+   Rust 支持操作符重载。

# 练习

+   为 `Interval` 实现 `PartialOrd` 特质。为了使代码简单，对于重叠的区间可以返回 `None`。

```rs
use interval::Interval;

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

    use std::fmt;
    impl<T: fmt::Display> fmt::Display for Interval<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "[{}, {}]", self.start, self.end)
        }
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

fn main() {
    use std::cmp::Ordering::{Equal, Greater, Less};

    let a = Interval::new(0, 1).unwrap();
    let b = Interval::new(0, 1).unwrap();
    assert_eq!(a.partial_cmp(&b), Some(Equal));
    assert_eq!(b.partial_cmp(&a), Some(Equal));

    let a = Interval::new(0, 1).unwrap();
    let b = Interval::new(2, 3).unwrap();
    assert_eq!(a.partial_cmp(&b), Some(Less));
    assert_eq!(b.partial_cmp(&a), Some(Greater));

    println!("Nice Work!");
}
```

<details><summary>解决方案</summary>

```rs
use interval::Interval;   pub mod interval {
 /// A list specifying general categories of Interval errors. #[derive(Debug)] pub enum IntervalError { /// Start is not less than or equal to end StartEndRangeInvalid, /// Two intervals to be merged do not overlap NonOverlappingInterval, }   /// A closed-interval [`start`, `end`] type used for representing a range of /// values between `start` and `end` inclusively. /// /// # Examples /// /// You can create an `Interval` using `new`. /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ #[derive(Debug, PartialEq)] pub struct Interval<T> { pub start: T, pub end: T, }   use std::fmt; impl<T: fmt::Display> fmt::Display for Interval<T> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result { write!(f, "[{}, {}]", self.start, self.end) } }      use std::cmp::Ordering;
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
  impl<T: Copy + PartialOrd> Interval<T> { /// Creates a new `Interval` set to `start` and `end`. /// /// # Examples /// /// ~~~rs /// let interval = Interval::new(1, 10).unwrap(); /// assert_eq!(interval.start, 1); /// assert_eq!(interval.end, 10); /// ~~~ pub fn new(start: T, end: T) -> Result<Self, IntervalError> { if start <= end { Ok(Self { start, end }) } else { Err(IntervalError::StartEndRangeInvalid) } }   /// Checks if two intervals overlap. Overlapping intervals have at least /// one point in common. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 5).unwrap(); /// let b = Interval::new(2, 4).unwrap(); /// assert_eq!(a.overlaps(&b), true); /// assert_eq!(b.overlaps(&a), true); /// ~~~ /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(4, 6).unwrap(); /// assert_eq!(a.overlaps(&b), false); /// assert_eq!(b.overlaps(&a), true); /// ~~~ pub fn overlaps(&self, other: &Interval<T>) -> bool { self.end >= other.start }   /// Merges two intervals returning a new `Interval`. /// /// The merged `Interval` range includes the union of ranges from each /// `Interval`. /// /// # Examples /// /// ~~~rs /// let a = Interval::new(1, 3).unwrap(); /// let b = Interval::new(3, 5).unwrap(); /// let c = a.merge(&b).unwrap(); /// assert_eq!(c.start, 1); /// assert_eq!(c.end, 5); /// ~~~ pub fn merge(&self, other: &Self) -> Result<Self, IntervalError> { if self.overlaps(other) { Ok(Self { start: self.start, end: other.end, }) } else { Err(IntervalError::NonOverlappingInterval) } } } }
  fn main() {
 use std::cmp::Ordering::{Equal, Greater, Less};   let a = Interval::new(0, 1).unwrap(); let b = Interval::new(0, 1).unwrap(); assert_eq!(a.partial_cmp(&b), Some(Equal)); assert_eq!(b.partial_cmp(&a), Some(Equal));   let a = Interval::new(0, 1).unwrap(); let b = Interval::new(2, 3).unwrap(); assert_eq!(a.partial_cmp(&b), Some(Less)); assert_eq!(b.partial_cmp(&a), Some(Greater));   println!("Nice Work!"); }
```</details>

# 下一节

现在我们已经介绍了特质，在继续探索属性之前，让我们确保我们的项目是同步的。

下面是完成后的代码：

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

* * *

1.  https://doc.rust-lang.org/rust-by-example/trait.html ↩

1.  这是一个单独的主题，你可以在[Rust 编程语言](https://doc.rust-lang.org/stable/book/)的[使用生命周期验证引用](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)部分和[Rust By Example](https://doc.rust-lang.org/rust-by-example/)的[生命周期](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html)部分中了解更多信息。↩
