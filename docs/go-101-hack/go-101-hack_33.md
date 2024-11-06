# 函数字面量

## 函数字面量

函数字面量只是表示一个匿名函数。你可以将函数字面量赋值给一个变量：

```
package main

import (
    "fmt"
)

func main() {
    f := func() { fmt.Println("Hello, 中国！") }
    f()
} 
```

或直接调用函数字面量（请注意函数字面量末尾的`()`）：

```
package main

import (
    "fmt"
)

func main() {
    func() { fmt.Println("Hello, 中国！") }()
} 
```

上述的`2`个程序都输出"`Hello, 中国！`"。

函数字面量也是一个闭包，因此它可以访问其周围函数的变量。检查以下示例，你真正想要的是打印`1`和`2`：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    for i := 1; i <= 2; i++ {
        go func() {fmt.Println(i)}()
    }
    time.Sleep(time.Second)
} 
```

但输出是：

```
3
3 
```

原因是`func`协程在`main`协程休眠之前没有运行的机会，而在那时，变量`i`已经被改变为`3`。将上述程序修改如下：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    for i := 1; i <= 2; i++ {
        go func() {fmt.Println(i)}()
        time.Sleep(time.Second)
    }
} 
```

`func`协程可以在`i`被改变之前运行，因此运行结果是你期望的：

```
1
2 
```

但惯用方法应该是将`i`作为函数字面量的参数传递：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    for i := 1; i <= 2; i++ {
        go func(i int) {fmt.Println(i)}(i)
    }
    time.Sleep(time.Second)
} 
```

在上述程序中，当执行"`go func(i int) {fmt.Println(i)}(i)`"时（注意：不是执行协程。），`main()`中定义的`i`被赋值给`func`的局部参数`i`。结果是：

```
1
2 
```

P.S. 你应该注意，如果你传递了一个参数但没有使用它，`Go` 编译器不会报错，但闭包会使用从父函数继承的变量。这意味着以下语句：

```
go func(int) {fmt.Println(i)}(i) 
```

等同于：

```
go func() {fmt.Println(i)}() 
```

参考：

[Go 编程语言规范](https://golang.org/ref/spec#Function_literals);

[关于向闭包传递参数的问题](https://groups.google.com/forum/#!topic/golang-nuts/JXTEYyoPLio);

[为什么在 Golang 中在闭包体后面添加“()”？](http://stackoverflow.com/questions/16008604/why-add-after-closure-body-in-golang)。
