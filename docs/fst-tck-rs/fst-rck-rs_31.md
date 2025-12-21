# 使用进行时态的依赖关系

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/useing_dependencies.html`](https://freddiehaddad.github.io/fast-track-to-rust/useing_dependencies.html)

现在我们已经将 `regex` 包作为依赖项添加，我们准备好*使用*它（有意为之）。你可以通过完整路径名 `regex::Regex`（包::模块）来引用它，或者更常见的是，通过使用 `use`^(1) 关键字将模块引入作用域。

我们在 rustle 程序中就是这样做的：

```rs
use std::fs::File;
use std::io::Read;
use std::io::{BufRead, BufReader};
use std::process::exit;
```

通过使用 `use regex::Regex;` 将模块引入作用域，我们可以用 `Regex` 来引用它。

现在我们已经知道了如何向我们的项目添加依赖项并使用它们，是时候添加对正则表达式的支持了！

* * *

1.  `use` 关键字不仅能将事物引入作用域，所以请确保查看有关 [use 声明](https://doc.rust-lang.org/reference/items/use-declarations.html) 的文档以获取关于 `use` 的更多详细信息。↩
