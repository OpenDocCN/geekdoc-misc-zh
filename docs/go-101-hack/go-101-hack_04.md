# “go build” 和 “go install”

# “go build” 和 “go install”

* * *

让我们整理一下 `$GOPATH` 目录，并且只保留 `Go` 源代码文件：

```
# tree
.
├── bin
├── pkg
└── src
    ├── greet
    │   └── greet.go
    └── hello
        └── hello.go

5 directories, 2 files 
```

`greet.go` 是一个 `greet` 包，只提供了一个函数：

```
# cat src/greet/greet.go
package greet

import "fmt"

func Greet() {
        fmt.Println("Hello 中国!")
} 
```

而 `hello.go` 是一个 `main` 包，利用了 `greet` 并且可以构建成一个可执行的二进制文件：

```
# cat src/hello/hello.go
package main

import "greet"

func main() {
        greet.Greet()
} 
```

(1) 进入 `src/hello` 目录，并执行 `go build` 命令：

```
# pwd
/root/gowork/src/hello
# go build
# ls
hello  hello.go
# ./hello
Hello 中国! 
```

我们可以看到当前目录下生成了一个全新的 `hello` 命令。

检查 `$GOPATH` 目录：

```
# tree
.
├── bin
├── pkg
└── src
    ├── greet
    │   └── greet.go
    └── hello
        ├── hello
        └── hello.go

5 directories, 3 files 
```

与执行 `go build` 前相比，只多了一个最终的可执行命令。

(2) 再次清理 `$GOPATH` 目录：

```
# tree
.
├── bin
├── pkg
└── src
    ├── greet
    │   └── greet.go
    └── hello
        └── hello.go

5 directories, 2 files 
```

在 `hello` 目录中运行 `go install`：

```
# pwd
/root/gowork/src/hello
# go install
# 
```

现在检查 `$GOPATH` 目录：

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

不仅生成了 `hello` 命令并放入 `bin` 目录中，还有一个 `greet.a` 放在 `pkg/linux_amd64` 中。而 `src` 文件夹保持清洁，只有源代码文件，并且没有变化。

(3) 在 `go build` 命令中有一个 `-i` 标志，它将安装目标依赖的包，但不会安装目标本身。让我们来检查一下：

```
# tree
.
├── bin
├── pkg
└── src
    ├── greet
    │   └── greet.go
    └── hello
        └── hello.go

5 directories, 2 files 
```

在 `hello` 目录下运行 `go build -i`：

```
# pwd
#/root/gowork/src/hello
# go build -i 
```

现在检查 `$GOPATH`：

```
# tree
.
├── bin
├── pkg
│   └── linux_amd64
│       └── greet.a
└── src
    ├── greet
    │   └── greet.go
    └── hello
        ├── hello
        └── hello.go 
```

除了 `src/hello` 目录中的 `hello` 命令外，还在 `pkg/linux_amd64` 中生成了一个 `greet.a` 库。

(4) 默认情况下，`go build` 使用目录的名称作为编译后二进制文件的名称，要修改它，可以使用 `-o` 标志：

```
# pwd
/root/gowork/src/hello
# go build -o he
# ls
he  hello.go 
```

现在，该命令是 `he`，而不是 `hello`。
