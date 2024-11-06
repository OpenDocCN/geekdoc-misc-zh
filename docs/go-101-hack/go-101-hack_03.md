# 包

# 包

* * *

在`Go`中，包可以分为`2`类：

(1) `main`包：用于生成可执行二进制文件，`main`函数是程序的入口点。以`hello.go`为例：

```
package main

import "greet"

func main() {
    greet.Greet()
} 
```

(2) 该类别还包括`2`种类型：

a) 库包：用于生成可以被其他人重用的目标文件。以`greet.go`为例：

```
package greet

import "fmt"

func Greet() {
    fmt.Println("Hello 中国!")
} 
```

b) 一些其他用于特殊目的的包，例如测试。

几乎每个程序都需要`Go`标准（`$GOROOT`）或第三方（`$GOPATH`）包。要使用它们，你应该使用`import`语句：

```
import "fmt"
import "github.com/NanXiao/stack" 
```

或者：

```
import (
    "fmt"
    "github.com/NanXiao/stack"
) 
```

在上述示例中，“`fmt`”和“`github.com/NanXiao/stack`”被称为`import path`，用于找到相关包。

你可能也会看到以下情况：

```
import m "lib/math" // use m as the math package name
import . "lib/math" // Omit package name when using math package 
```

如果`go install`命令找不到指定的包，它会抱怨如下的错误消息：

```
... : cannot find package "xxxx" in any of:
        /usr/local/go/src/xxxx (from $GOROOT)
        /root/gowork/src/xxxx (from $GOPATH) 
```

为了避免库冲突，最好让你自己的包的路径成为世界上唯一的：例如，你的`github`仓库目标：

```
 github.com/NanXiao/... 
```

**惯例上**，你的包名应该与`import path`中的最后一项相同；虽然这不是必须的，但这是一个很好的编码习惯。

参考：

[《Go 编程语言》](http://www.gopl.io/)。
