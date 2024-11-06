# 创建 Go 工作空间

# 创建 Go 工作空间

* * *

一旦`Go`构建环境准备好了，下一步是创建开发工作空间：

(1) 设置一个新的空目录：

```
# mkdir gowork 
```

(2) 使用一个新的环境变量`$GOPATH`来指向它：

```
# cat /etc/profile
......
GOPATH=/root/gowork
export GOPATH
...... 
```

工作空间应包含`3`个子目录：

> src：包含 Go 源代码。
> 
> pkg：包含包对象。你可以将它们视为在链接阶段用于生成最终可执行文件的库。
> 
> bin：包含可执行文件。

让我们看一个例子：

(1) 在我的系统中，在`$GOPATH`中创建一个`src`目录，它是`/root/gowork`：

```
# mkdir src
# tree
.
└── src

1 directory, 0 files 
```

(2) 由于`Go`使用"`package`"的概念来组织源代码，每个"`package`"都应占据一个不同的目录，所以我在`src`中创建了一个`greet`目录：

```
# mkdir src/greet 
```

然后在`src/greet`中创建一个新的`Go`源代码文件(`greet.go`)：

```
# cat src/greet/greet.go
package greet

import "fmt"

func Greet() {
        fmt.Println("Hello 中国!")
} 
```

你可以考虑这个`greet`目录提供了一个`greet`包，其他程序可以使用它。

(3) 创建另一个使用`greet`包的包`hello`：

```
# mkdir src/hello
# cat src/hello/hello.go
package main

import "greet"

func main() {
        greet.Greet()
} 
```

在`hello.go`中，`main`函数调用了`greet`包提供的`Greet`函数。

(4) 现在我们的`$GOPATH`布局如下：

```
# tree
.
└── src
    ├── greet
    │   └── greet.go
    └── hello
        └── hello.go

3 directories, 2 files 
```

让我们编译并安装`hello`包：

```
# go install hello 
```

再次检查`$GOPATH`的布局：

```
# tree
.
├── bin
│   └── hello
├── pkg
│   └── linux_amd64
│       └── greet.a
└── src
    ├── greet
    │   └── greet.go
    └── hello
        └── hello.go

6 directories, 4 files 
```

可以看到可执行命令`hello`生成在`bin`文件夹中。因为`hello`需要`greet`包的帮助，所以在`pkg`目录下也会生成一个`greet.a`对象，但在系统相关的子目录中：`linux_amd64`。

运行`hello`命令：

```
# ./bin/hello
Hello 中国! 
```

一切都正常工作！

(5) 你应该将`$GOPATH/bin`添加到`$PATH`环境变量以方便：

```
PATH=$PATH:$GOPATH/bin
export PATH 
```

然后你可以直接运行`hello`：

```
# hello
Hello 中国! 
```

参考：

[如何编写 Go 代码](https://golang.org/doc/code.html)。
