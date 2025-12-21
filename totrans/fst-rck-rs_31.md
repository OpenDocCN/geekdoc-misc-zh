# use-ing Dependencies

> 原文：[https://freddiehaddad.github.io/fast-track-to-rust/useing_dependencies.html](https://freddiehaddad.github.io/fast-track-to-rust/useing_dependencies.html)

Now that we've added the `regex` crate as a dependency, we are ready to *use* it (pun intended). You can refer to the crate by the full path name `regex::Regex` (crate::module) or, more commonly, by bringing the module into scope with the `use`^([1](#footnote-1)) keyword.

We've been doing this in our rustle program:

```rs
use std::fs::File;
use std::io::Read;
use std::io::{BufRead, BufReader};
use std::process::exit;
```

By bringing the module into scope with `use regex::Regex;`, we can reference it with `Regex`.

Now that we know how to add dependencies to our project and use them, it's time to add support for regular expressions!

* * *

1.  The [`use`](https://doc.rust-lang.org/std/keyword.use.html) keyword can do more than just bring things into scope, so be sure to check the documentation on [use declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) for more details on [`use`](https://doc.rust-lang.org/std/keyword.use.html). [↩](#fr-1-1)