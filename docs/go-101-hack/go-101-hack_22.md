# 类型断言和类型开关

# 类型断言和类型开关

* * *

有时，您可能想知道接口变量的确切类型。在这种情况下，您可以使用`类型断言`：

```
x.(T) 
```

`x`是其类型必须为**接口**的变量，`T`是您要检查的类型。例如：

```
package main

import "fmt"

func printValue(v interface{}) {
    fmt.Printf("The value of v is: %v", v.(int))
}

func main() {
    v := 10
    printValue(v)
} 
```

运行结果是：

```
The value of v is: 10 
```

在上面的示例中，使用`v.(int)`来断言`v`是`int`变量。

如果`类型断言`操作失败，将会发生运行时恐慌：更改

```
fmt.Printf("The value of v is: %v", v.(int)) 
```

为：

```
fmt.Printf("The value of v is: %v", v.(string)) 
```

然后执行程序将会得到以下错误：

```
panic: interface conversion: interface is int, not string

goroutine 1 [running]:
panic(0x4f0840, 0xc0820042c0)
...... 
```

为了避免这种情况，`类型断言`实际上返回一个额外的`布尔`变量来告诉此操作是否成立。因此，修改程序如下：

```
package main

import "fmt"

func printValue(v interface{}) {
    if v, ok := v.(string); ok {
        fmt.Printf("The value of v is: %v", v)
    } else {
        fmt.Println("Oops, it is not a string!")
    }

}

func main() {
    v := 10
    printValue(v)
} 
```

这次，输出是：

```
Oops, it is not a string! 
```

此外，您还可以使用`类型开关`，它利用`类型断言`来确定变量的类型，并根据需要执行操作。请查看以下示例：

```
package main

import "fmt"

func printValue(v interface{}) {
    switch v := v.(type) {
    case string:
        fmt.Printf("%v is a string\n", v)
    case int:
        fmt.Printf("%v is an int\n", v)
    default:
        fmt.Printf("The type of v is unknown\n")
    }
}

func main() {
    v := 10
    printValue(v)
} 
```

运行结果在此：

```
10 is an int 
```

与`类型断言`相比，`类型开关`在括号中使用关键字`type`而不是指定的变量类型（如`int`）。

参考资料：

[Effective Go](https://golang.org/doc/effective_go.html)；

[Go – x.(T)类型断言](https://codingair.wordpress.com/2014/07/21/go-x-t-type-assertions/)；

[如何在 Golang 中找到对象的类型？](http://stackoverflow.com/questions/20170275/how-to-find-a-type-of-a-object-in-golang)。
