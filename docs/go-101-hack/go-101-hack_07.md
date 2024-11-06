# 初始化函数

## 初始化函数

有一个`init()`函数，顾名思义，它将做一些初始化工作，例如初始化可能不容易表达的变量，或者校准程序状态。一个文件可以包含一个或多个`init()`函数，如下所示：

```
package main

import "fmt"

var global int = 0

func init() {
    global++
    fmt.Println("In first Init(), global is: ", global)
}

func init() {
    global++
    fmt.Println("In Second Init(), global is: ", global)
}

func main() {
    fmt.Println("In main(), global is: ", global)
} 
```

执行结果如下：

```
In first Init(), global is:  1
In Second Init(), global is:  2
In main(), global is:  2 
```

由于一个包可以包含多个文件，可能会有许多`init()`函数。你**不应该**假设哪个文件的`init()`函数先执行。唯一有保证的是包中声明的变量将在该包中的所有`init()`函数执行之前求值。

看另一个例子。`$GOROOT/src`目录如下所示：

```
# tree
.
├── foo
│   └── foo.go
└── play
    └── main.go 
```

有`2`个简单的包：`foo`和`play`。`foo/foo.go`在这里：

```
package foo

import "fmt"

var Global int

func init() {
        Global++
        fmt.Println("foo init() is called, Global is: ", Global)
} 
```

当`play/main.go`为：

```
package main

import "foo"

func main() {
} 
```

构建`play`命令：

```
# go install play
# play
src/play/main.go:3: imported and not used: "foo" 
```

此错误的原因是`main.go`没有使用`foo`包导出的任何函数或变量。因此，如果你只想执行一个导入包的`init()`函数，并且不想使用包的其他内容，你应该将"`import "foo"`"修改为"`import _ "foo"`"：

```
 package main

import _ "foo"

func main() {
} 
```

现在构建过程将会成功，而且`play`命令的输出如下所示：

```
# play
foo init() is called, Global is:  1 
```

参考文献：

[Effective Go](https://golang.org/doc/effective_go.html#init);

[Go 中的 init() 函数是何时运行的？](http://stackoverflow.com/questions/24790175/when-is-the-init-function-in-go-golang-run).
