# 调试

## 调试

没有人能写出无 bug 的代码，所以调试是每个软件工程师必备的技能。以下是关于调试`Go`程序的一些技巧：

(1) 打印

是的！打印日志似乎是最简单的方法，但实际上在大多数情况下它是最有效的方法。`Go`在[fmt](https://golang.org/pkg/fmt/)包中提供了一大家族的打印函数，而且整洁地使用它们是你应该掌握的专业技能。

(2) 调试器

在某些情况下，也许你需要专门的调试工具来帮助你找出根本原因。你可以使用`gdb`，但由于"`GDB 对 Go 程序的理解不够好。`"（来自[这里](https://golang.org/doc/gdb)），我建议使用[Delve](https://github.com/derekparker/delve)，一个专门为`Go`设计的调试器。

无论是使用`gdb`还是`Delve`，如果你想调试可执行文件，你必须在编译二进制文件时传递`-gcflags "-N -l"`来禁用代码优化，否则在调试过程中可能会发生一些奇怪的事情，比如你无法打印已声明变量的值。

除了调试预编译文件，`Delve`可以即时编译和调试代码，看下面的例子：

```
package main

import "fmt"

func main() {
    ch := make(chan int)
    go func(chan int) {
        for _, v := range []int{1, 2} {
            ch <- v
        }
        close(ch)
    }(ch)

    for v := range ch {
        fmt.Println(v)
    }
    fmt.Println("The channel is closed.")
} 
```

调试流程如下：

```
# dlv debug channel.go
Type 'help' for list of commands.
(dlv) b channel.go:14
Breakpoint 1 set at 0x401079 for main.main() ./channel.go:14
(dlv) c
> main.main() ./channel.go:14 (hits goroutine(1):1 total:1) (PC: 0x401079)
     9:                         ch <- v
    10:                 }
    11:                 close(ch)
    12:         }(ch)
    13:
=>  14:         for v := range ch {
    15:                 fmt.Println(v)
    16:         }
    17:         fmt.Println("The channel is closed.")
    18: }
(dlv) n
> main.main() ./channel.go:15 (PC: 0x4010c9)
    10:                 }
    11:                 close(ch)
    12:         }(ch)
    13:
    14:         for v := range ch {
=>  15:                 fmt.Println(v)
    16:         }
    17:         fmt.Println("The channel is closed.")
    18: }
(dlv) p v
1
(dlv) goroutine
Thread 12380 at ./channel.go:15
Goroutine 1:
        Runtime: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x42a283)
        User: ./channel.go:15 main.main (0x4010c9)
        Go: /usr/local/go/src/runtime/asm_amd64.s:145 runtime.rt0_go (0x453321)
(dlv) goroutines
[5 goroutines]
* Goroutine 1 - User: ./channel.go:15 main.main (0x4010c9)
  Goroutine 2 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x42a283)
  Goroutine 3 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x42a283)
  Goroutine 4 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x42a283)
  Goroutine 5 - User: ./channel.go:9 main.main.func1 (0x4013a8)
(dlv) 
```

与`gdb`相比，`Delve`不提供`start`命令，所以你需要先设置断点，然后运行`continue`命令。你可以看到，`Delve`提供了丰富的命令，例如，你可以检查每个 goroutine 的状态，所以我认为你应该经常练习它，你会喜欢它的！

开心调试！
