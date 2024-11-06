# Goroutine

## Goroutine

运行中的`Go`程序由一个或多个 goroutine 组成，每个 goroutine 都可以被视为一个独立的任务。 Goroutine 和线程有许多共同点，例如：每个 goroutine（线程）都有其私有的堆栈和寄存器；如果主 goroutine（线程）退出，则程序将退出，等等。但是在现代操作系统（例如，`Linux`）上，实际执行和调度的单位是线程，因此如果 goroutine 希望变为运行状态，它必须“附加”到一个线程。让我们看一个例子：

```
package main

import (
    "time"
)

func main() {
    time.Sleep(1000 * time.Second)
} 
```

程序的作用只是睡一会儿，不做任何有用的事情。在`Linux`上启动它，使用`Delve`附加到正在运行的进程并观察其详细信息：

```
(dlv) threads
* Thread 1040 at 0x451f73 /usr/local/go/src/runtime/sys_linux_amd64.s:307 runtime.futex
  Thread 1041 at 0x451f73 /usr/local/go/src/runtime/sys_linux_amd64.s:307 runtime.futex
  Thread 1042 at 0x451f73 /usr/local/go/src/runtime/sys_linux_amd64.s:307 runtime.futex
  Thread 1043 at 0x451f73 /usr/local/go/src/runtime/sys_linux_amd64.s:307 runtime.futex
  Thread 1044 at 0x451f73 /usr/local/go/src/runtime/sys_linux_amd64.s:307 runtime.futex 
```

我们可以看到该进程有`5`个线程，请通过检查`/proc/1040/task/`目录来确认：

```
# cd /proc/1040/task/
# ls
1040  1041  1042  1043  1044 
```

是的，`Delve`的线程信息是正确的！检查 goroutine 的细节：

```
(dlv) goroutines
[4 goroutines]
  Goroutine 1 - User: /usr/local/go/src/runtime/time.go:59 time.Sleep (0x43e236)
  Goroutine 2 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x426f73)
  Goroutine 3 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x426f73)
* Goroutine 4 - User: /usr/local/go/src/runtime/lock_futex.go:206 runtime.notetsleepg (0x40b1ce) 
```

只有一个`main` goroutine，其他`3`个 goroutine 到底是什么鬼？实际上，其他`3`个 goroutine 是系统 goroutine，你可以参考相关信息[这里](https://github.com/derekparker/delve/issues/553)。`main` goroutine 的数量是`1`，你可以检查它：

```
(dlv) goroutine 1
Switched from 4 to 1 (thread 1040)
(dlv) bt
0  0x0000000000426f73 in runtime.gopark
   at /usr/local/go/src/runtime/proc.go:263
1  0x0000000000426ff3 in runtime.goparkunlock
   at /usr/local/go/src/runtime/proc.go:268
2  0x000000000043e236 in time.Sleep
   at /usr/local/go/src/runtime/time.go:59
3  0x0000000000401013 in main.main
   at ./gocode/src/goroutine.go:8
4  0x0000000000426b9b in runtime.main
   at /usr/local/go/src/runtime/proc.go:188
5  0x0000000000451000 in runtime.goexit
   at /usr/local/go/src/runtime/asm_amd64.s:1998 
```

使用`go`关键字可以创建并启动一个 goroutine，看另一个案例：

```
package main

import (
    "fmt"
    "time"
)

func main() {
    ch := make(chan int)

    go func(chan int) {
        var count int
        for {
            count++
            ch <- count
            time.Sleep(10 * time.Second)
        }
    }(ch)

    for v := range ch {
        fmt.Println(v)
    }
} 
```

`go func`语句生成另一个作为生产者的 goroutine；而`main` goroutine 则作为消费者。输出应该是：

```
1
2
...... 
```

使用`Delve`检查 goroutine 方面：

```
(dlv) goroutines
[6 goroutines]
  Goroutine 1 - User: ./gocode/src/goroutine.go:20 main.main (0x40106c)
  Goroutine 2 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x429fc3)
  Goroutine 3 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x429fc3)
  Goroutine 4 - User: /usr/local/go/src/runtime/proc.go:263 runtime.gopark (0x429fc3)
  Goroutine 5 - User: /usr/local/go/src/runtime/time.go:59 time.Sleep (0x442ab6)
* Goroutine 6 - User: /usr/local/go/src/runtime/lock_futex.go:206 runtime.notetsleepg (0x40cf4e)
(dlv) goroutine 1
Switched from 6 to 1 (thread 1997)
(dlv) bt
0  0x0000000000429fc3 in runtime.gopark
   at /usr/local/go/src/runtime/proc.go:263
1  0x000000000042a043 in runtime.goparkunlock
   at /usr/local/go/src/runtime/proc.go:268
2  0x00000000004047eb in runtime.chanrecv
   at /usr/local/go/src/runtime/chan.go:470
3  0x0000000000404354 in runtime.chanrecv2
   at /usr/local/go/src/runtime/chan.go:360
4  0x000000000040106c in main.main
   at ./gocode/src/goroutine.go:20
5  0x0000000000429beb in runtime.main
   at /usr/local/go/src/runtime/proc.go:188
6  0x0000000000455de0 in runtime.goexit
   at /usr/local/go/src/runtime/asm_amd64.s:1998
(dlv) goroutine 5
Switched from 1 to 5 (thread 1997)
(dlv) bt
0  0x0000000000429fc3 in runtime.gopark
   at /usr/local/go/src/runtime/proc.go:263
1  0x000000000042a043 in runtime.goparkunlock
   at /usr/local/go/src/runtime/proc.go:268
2  0x0000000000442ab6 in time.Sleep
   at /usr/local/go/src/runtime/time.go:59
3  0x00000000004011d6 in main.main.func1
   at ./gocode/src/goroutine.go:16
4  0x0000000000455de0 in runtime.goexit
   at /usr/local/go/src/runtime/asm_amd64.s:1998 
```

`main` goroutine 的数量是`1`，而`func`是`5`。

另一个你应该注意的警告是 goroutine 之间的切换点。它可以是阻塞的系统调用、通道操作等。

参考:

[Effective Go](https://golang.org/doc/effective_go.html#goroutines);

[没有事件循环的性能](http://dave.cheney.net/2015/08/08/performance-without-the-event-loop);

[Goroutines 如何工作](http://blog.nindalf.com/how-goroutines-work/)。
