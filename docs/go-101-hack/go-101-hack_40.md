# 选择操作

# 选择操作

* * *

`Go`的`select`操作看起来类似于`switch`，但专门用于轮询发送和接收操作的通道。查看以下示例：

```
package main

import (
        "fmt"
        "time"
)

func main() {
        ch1 := make(chan int)
        ch2 := make(chan int)

        go func(ch chan int) { <-ch }(ch1)
        go func(ch chan int) { ch <- 2 }(ch2)

        time.Sleep(time.Second)

        for {
                select {
                case ch1 <- 1:
                        fmt.Println("Send operation on ch1 works!")
                case <-ch2:
                        fmt.Println("Receive operation on ch2 works!")
                default:
                        fmt.Println("Exit now!")
                        return
                }
        }
} 
```

运行结果如下：

```
Send operation on ch1 works!
Receive operation on ch2 works!
Exit now! 
```

`select`操作将检查哪个`case`分支可以运行，这意味着发送或接收操作可以成功执行。如果现在有多个`case`准备就绪，`select`将随机选择一个来执行。如果没有`case`准备就绪，但有一个`default`分支，则将执行`default`块，否则`select`操作将阻塞。在上面的示例中，如果`main`协程不休眠（`time.Sleep(time.Second)`），其他`2 func`协程将无法获得运行的机会，因此`select`语句中只会执行`default`块。

`select`语句不会处理`nil`通道，因此如果用于接收操作的通道已关闭，您应将其值标记为`nil`，然后它将被从选择列表中移除。因此，对多个接收通道进行选择的常见模式如下所示：

```
for ch1 != nil && ch2 != nil {
    select {
    case x, ok := <-ch1:
        if !ok {
            ch1 = nil
            break
        }
        ......
    case x, ok := <-ch2:
        if !ok {
            ch2 = nil
            break
        }
        ......
    }
} 
```

参考：

[Go 编程语言规范](https://golang.org/ref/spec);

[当所有通道关闭时跳出选择语句](http://stackoverflow.com/questions/13666253/breaking-out-of-a-select-statement-when-all-channels-are-closed);

[好奇的通道](http://dave.cheney.net/2013/04/30/curious-channels).
