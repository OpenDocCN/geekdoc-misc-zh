# 错误 vs 错误

## 错误 vs 错误

处理错误是编写健壮程序的关键部分。在扫描`Go`包时，经常会看到其中有多个返回值，其中包含一个错误。例如：

> func Open(name string) (*File, error)
> 
> Open 打开指定的文件以供读取。如果成功，返回的文件上的方法可用于读取；相关文件描述符的模式为 O_RDONLY。如果出现错误，它将是*PathError 类型。

使用`os.Open`函数的惯用方法如下：

```
file, err := os.Open("file.go") // For read access.
if err != nil {
    log.Fatal(err)
} 
defer file.Close() 
```

因此，为了实现弹性的`Go`程序，如何生成和处理错误是一门必修课程。

`Go`提供了`error`和`errors`两种，你不应该混淆它们。`error`是一个内置的接口类型：

```
type error interface {
    Error() string
} 
```

因此，对于任何类型，只要实现了`Error() string`方法，它就会自动满足`error`接口。`errors`是我最喜欢的包之一，因为它非常简单（如果每个包都类似于`errors`，生活肯定会更轻松！）。去掉注释后，核心代码行数非常少：

```
package errors

func New(text string) error {
    return &errorString{text}
}

type errorString struct {
    s string
}

func (e *errorString) Error() string {
    return e.s
} 
```

`errors`包中的`New`函数返回一个符合`error`接口的`errorString`结构体。查看以下示例：

```
package main

import (
    "errors"
    "fmt"
)

func maxElem(s []int) (int, error) {
    if len(s) == 0 {
        return 0, errors.New("The slice must be non-empty!")
    }

    max := s[0]
    for _, v := range s[1:] {
        if v > max {
            max = v
        }
    }
    return max, nil
}

func main() {
    s := []int{}
    _, err := maxElem(s)
    if err != nil {
        fmt.Println(err)
    }
} 
```

执行结果在这里：

```
The slice must be non-empty! 
```

在实际生活中，你可能更喜欢使用`fmt`包中定义的`Errorf`函数来创建`error`接口，而不是直接使用`errors.New()`：

> func Errorf(format string, a ...interface{}) error
> 
> Errorf 根据格式说明符进行格式化，并返回作为满足错误的值的字符串。

因此，上述代码可以重构如下：

```
func maxElem(s []int) (int, error) {
    ......
    if len(s) == 0 {
        return 0, fmt.Errorf("The slice must be non-empty!")
    }
    ......
} 
```

参考资料：

[《Go 编程语言》](http://www.gopl.io/)。
