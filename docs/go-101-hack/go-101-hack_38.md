# 无缓冲和有缓冲的通道

## 无缓冲和有缓冲的通道

通道分为两类：无缓冲和有缓冲。

(1) 无缓冲通道

对于无缓冲通道，发送者会在通道上阻塞，直到接收者从通道接收数据，而接收者也会在通道上阻塞，直到发送者将数据发送到通道中。请查看以下示例：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    ch := make(chan int)

    go func(ch chan int) {
        fmt.Println("Func goroutine begins sending data")
        ch <- 1
        fmt.Println("Func goroutine ends sending data")
     }(ch)

    fmt.Println("Main goroutine sleeps 2 seconds")
    time.Sleep(time.Second * 2)

    fmt.Println("Main goroutine begins receiving data")
    d := <- ch
    fmt.Println("Main goroutine received data:", d)

    time.Sleep(time.Second)
} 
```

运行结果如下：

```
Main goroutine sleeps 2 seconds
Func goroutine begins sending data
Main goroutine begins receiving data
Main goroutine received data: 1
Func goroutine ends sending data 
```

在启动`main`协程之后，它会立即进入睡眠（打印"`Main goroutine sleeps 2 seconds`"），这会导致`main`协程让出`CPU`给`func`协程（打印"`Func goroutine begins sending data`"）。但由于`main`协程正在睡眠，无法从通道接收数据，所以`func`协程中的`ch <- 1`操作无法完成，直到`main`协程中的`d := <- ch`被执行（打印最后的`3`条日志）。

(2) 有缓冲通道

与无缓冲通道相比，有缓冲通道的发送者将在`通道`没有空槽位时阻塞，而接收者将在通道为空时阻塞。修改上述示例：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    ch := make(chan int, 2)

    go func(ch chan int) {
        for i := 1; i <= 5; i++ {
            ch <- i
            fmt.Println("Func goroutine sends data: ", i)
        }
        close(ch)
    }(ch)

    fmt.Println("Main goroutine sleeps 2 seconds")
    time.Sleep(time.Second * 2)

    fmt.Println("Main goroutine begins receiving data")
    for d := range ch {
        fmt.Println("Main goroutine received data:", d)
    }
} 
```

执行结果如下：

```
Main goroutine sleeps 2 seconds
Func goroutine sends data:  1
Func goroutine sends data:  2
Main goroutine begins receiving data
Main goroutine received data: 1
Main goroutine received data: 2
Main goroutine received data: 3
Func goroutine sends data:  3
Func goroutine sends data:  4
Func goroutine sends data:  5
Main goroutine received data: 4
Main goroutine received data: 5 
```

在这个示例中，由于通道有`2`个槽位，所以`func`协程在发送第三个元素之前不会阻塞。

P.S.，“`make(chan int, 0)`”等同于“`make(chan int)`”，它也会创建一个无缓冲的`int`通道。
