# 短变量声明

# 短变量声明

* * *

短变量声明是在 `Go` 中“声明变量”的一种非常便利的方式：

```
i := 10 
```

这是以下内容的缩写（请注意没有类型）：

```
var i = 10 
```

`Go` 编译器将根据变量的值推断类型。这是一个非常方便的特性，但另一方面，它也带来了一些你应该注意的陷阱：

（1）此格式只能在函数中使用：

```
package main

i := 10

func main() {
    fmt.Println(i)
} 
```

编译器将抱怨以下内容：

```
syntax error: non-declaration statement outside function body 
```

（2）你必须声明**至少 1 个新变量**：

```
package main

import "fmt"

func main() {
    var i = 1

    i, err := 2, true

    fmt.Println(i, err)
} 
```

在 `i, err := 2, false` 语句中，只有 `err` 是一个新声明的变量，`var` 实际上在 `var i = 1` 中声明。

（3）短变量声明可以遮蔽全局变量声明，这可能不是你想要的，会带来很大的惊喜：

```
package main

import "fmt"

var i = 1

func main() {

    i, err := 2, true

    fmt.Println(i, err)
} 
```

`i, err := 2, true` 实际上声明了一个**新的本地 i**，这使得 `main` 函数中的**全局 i** 不可访问。要使用全局变量而不引入新的本地变量，可能的一个解决方案是这样的：

```
package main

import "fmt"

var i int

func main() {

    var err bool

    i, err = 2, true

    fmt.Println(i, err)
} 
```

参考：

[短变量声明](https://golang.org/ref/spec#Short_variable_declarations)。
