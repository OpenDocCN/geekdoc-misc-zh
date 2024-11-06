# 空通道 VS 关闭的通道

# 空通道 VS 关闭的通道

* * *

通道类型的零值是`nil`，在`nil`通道上的发送和接收操作将始终阻塞。请查看以下示例：

```
package main

import "fmt"

func main() {
        var ch chan int

        go func(c chan int) {
                for v := range c {
                        fmt.Println(v)
                }
        }(ch)

        ch <- 1
} 
```

运行结果如下：

```
fatal error: all goroutines are asleep - deadlock!

goroutine 1 [chan send (nil chan)]:
main.main()
        /root/nil_channel.go:14 +0x64

goroutine 5 [chan receive (nil chan)]:
main.main.func1(0x0)
        /root/nil_channel.go:9 +0x53
created by main.main
        /root/nil_channel.go:12 +0x37 
```

我们可以看到`main`和`func`协程都被阻塞了。

`Go`内置的`close`函数可用于关闭通道，该通道不得是只接收的，并且应始终由发送方执行，而不是接收方。关闭`nil`通道将引发恐慌。请参考以下示例：

```
package main

func main() {
        var ch chan int
        close(ch)
} 
```

运行结果如下：

```
panic: close of nil channel

goroutine 1 [running]:
panic(0x456500, 0xc82000a170)
 /usr/local/go/src/runtime/panic.go:481 +0x3e6
main.main()
 /root/nil_channel.go:5 +0x1e 
```

此外，还有一些操作已关闭通道的微妙之处：

(1) 关闭已关闭的通道也会引发恐慌：

```
package main

func main() {
        ch := make(chan int)
        close(ch)
        close(ch)
} 
```

运行结果如下：

```
panic: close of closed channel

goroutine 1 [running]:
panic(0x456500, 0xc82000a170)
 /usr/local/go/src/runtime/panic.go:481 +0x3e6
main.main()
 /root/nil_channel.go:6 +0x4d 
```

(2) 在关闭的通道上发送也会引发恐慌：

```
package main

func main() {
        ch := make(chan int)
        close(ch)
        ch <- 1
} 
```

运行结果如下：

```
panic: send on closed channel

goroutine 1 [running]:
panic(0x456500, 0xc82000a170)
 /usr/local/go/src/runtime/panic.go:481 +0x3e6
main.main()
 /root/nil_channel.go:6 +0x6c 
```

(3) 在关闭的通道上接收将返回通道类型的零值而不会阻塞：

```
package main

import "fmt"

func main() {
        ch := make(chan int)
        close(ch)
        fmt.Println(<-ch)
} 
```

执行结果如下：

```
0 
```

以下是"`nil`通道 VS 关闭的通道"的总结：

| 操作类型 | Nil 通道 | 关闭的通道 |
| --- | --- | --- |
| 发送 | 阻塞 | 恐慌 |
| 接收 | 阻塞 | 不阻塞，返回通道类型的零值 |
| 关闭 | 恐慌 | 恐慌 |

参考资料：

[内置包](https://golang.org/pkg/builtin/#close);

[留下一个通道是可以的吗？](http://stackoverflow.com/questions/8593645/is-it-ok-to-leave-a-channel-open);

[Go 编程语言规范](https://golang.org/ref/spec).
