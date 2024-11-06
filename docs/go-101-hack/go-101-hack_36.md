# 在通道上进行发送和接收操作

# 在通道上进行发送和接收操作

* * *

`Go`内置的`channel`类型提供了一种便利的通信和同步方法：生产者将数据推入通道，而消费者从中拉取数据。

通道上的发送操作很简单，只要填入的东西是一个有效的表达式并且与通道的类型匹配即可：

```
Channel <- Expression 
```

以以下代码为例：

```
package main

func send() int {
    return 2
}
func main()  {
    ch := make(chan int, 2)
    ch <- 1
    ch <- send()
} 
```

在通道上的接收操作会从通道中拉取值，如果你不在乎得到了什么，可以保存或丢弃它。请看以下示例：

```
package main

import "fmt"

func main()  {
    ch := make(chan int)
    go func(ch chan int) {
        ch <- 1
        ch <- 2
    }(ch)
    <-ch
    fmt.Println(<-ch)
} 
```

运行结果为`2`，这是因为在`<-ch`语句中第一个值(`1`)被忽略了。

与其发送操作相比，接收操作有点棘手：在赋值和初始化中，会有另一个返回值，它表示这次通信是否成功。而这个变量的惯用命名是`ok`：

```
v, ok := <- ch 
```

如果接收到的值是通过成功的发送操作传递到通道的，`ok`的值为`true`，或者如果它是因为通道关闭并且为空而生成的零值，则为`false`。这意味着尽管通道已关闭，只要通道中仍有数据，接收操作当然可以从中获取东西。看以下代码：

```
package main

import "fmt"

func main()  {
    ch := make(chan int)

    go func(ch chan int) {
        ch <- 1
        ch <- 2
        close(ch)
    }(ch)

    for i := 1; i <= 3; i++ {
        v, ok := <- ch
        fmt.Printf("value is %d, ok is %v\n", v, ok)
    }
} 
```

执行结果如下：

```
value is 1, ok is true
value is 2, ok is true
value is 0, ok is false 
```

我们可以看到，当`func`协程执行关闭通道操作后，从通道获取的`v`的值是整数类型的零值：`0`，而`ok`是`false`。

参考：

[Go 语言规范](https://golang.org/ref/spec)。
