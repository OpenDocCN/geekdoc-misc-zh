# 装饰类型以实现 io.Reader 接口

## 装饰类型以实现 io.Reader 接口

[io 包](https://golang.org/pkg/io/)提供了一堆方便的读取函数和方法，但不幸的是，它们都要求参数满足[io.Reader](https://golang.org/pkg/io/#Reader)接口。看下面的例子：

```
package main

import (
    "fmt"
    "io"
)

func main() {
    s := "Hello, world!"
    p := make([]byte, len(s))
    if _, err := io.ReadFull(s, p); err != nil {
        fmt.Println(err)
    } else {
        fmt.Printf("%s\n", p)
    }
} 
```

编译上述程序会生成一个错误：

```
read.go:11: cannot use s (type string) as type io.Reader in argument to io.ReadFull:
    string does not implement io.Reader (missing Read method) 
```

[io.ReadFull](https://golang.org/pkg/io/#ReadFull)函数要求参数应符合`io.Reader`，但`string`类型不提供`Read()`方法，因此我们需要在`s`变量上做一些小技巧。将`io.ReadFull(s, p)`修改为`io.ReadFull(strings.NewReader(s), p)`：

```
package main

import (
    "fmt"
    "io"
    "strings"
)

func main() {
    s := "Hello, world!"
    p := make([]byte, len(s))
    if _, err := io.ReadFull(strings.NewReader(s), p); err != nil {
        fmt.Println(err)
    } else {
        fmt.Printf("%s\n", p)
    }
} 
```

这次，编译通过了，运行结果如下：

```
Hello, world! 
```

[strings.NewReader](https://golang.org/pkg/strings/#NewReader)函数将`string`转换为一个[strings.Reader](https://golang.org/pkg/bytes/#Reader)结构，该结构提供了一个[read](https://golang.org/pkg/bytes/#Reader.Read)方法：

```
func (r *Reader) Read(b []byte) (n int, err error) 
```

除了`string`，另一个常见操作是使用[bytes.NewReader](https://golang.org/pkg/bytes/#NewReader)将一个字节切片转换为一个[bytes.Reader](https://golang.org/pkg/bytes/#Reader)结构，该结构满足`io.Reader`接口。对上面的例子进行一些修改：

```
 package main

import (
    "bytes"
    "fmt"
    "io"
    "strings"
)

func main() {
    s := "Hello, world!"
    p := make([]byte, len(s))
    if _, err := io.ReadFull(strings.NewReader(s), p); err != nil {
        fmt.Println(err)
    }

    r := bytes.NewReader(p)
    if b, err := r.ReadByte(); err != nil {
        fmt.Println(err)
    } else {
        fmt.Printf("%c\n", b)
    }
} 
```

`bytes.NewReader`将`p`切片转换为一个`bytes.Reader`结构。输出如下：

```
H 
```
