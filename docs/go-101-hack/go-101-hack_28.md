# 检查数据竞争

# 检查数据竞争

* * *

"数据竞争"是并发程序中常见但臭名昭著的问题。有时很难调试和重现，特别是在一些大型系统中，这会让人非常沮丧。幸运的是，`Go`工具链提供了一个`race detector`（现在仅在`amd64`平台上可用），它可以帮助我们快速发现和修复这种问题，甚至可以节省我们的时间，甚至是生命！

以下经典的“数据竞争”程序作为例子：

```
package main

import (
        "fmt"
        "sync"
)

var global int
var wg sync.WaitGroup

func count() {
        defer wg.Done()
        for i := 0; i < 10000; i++{
                global++
        }
}

func main() {
        wg.Add(2)
        go count()
        go count()
        wg.Wait()
        fmt.Println(global)
} 
```

两个任务同时增加`global`变量，所以`global`的最终值是不确定的。使用`race detector`来检查它：

```
# go run -race race.go
==================
WARNING: DATA RACE
Read by goroutine 7:
  main.count()
      /root/gocode/src/race.go:14 +0x6d

Previous write by goroutine 6:
  main.count()
      /root/gocode/src/race.go:14 +0x89

Goroutine 7 (running) created at:
  main.main()
      /root/gocode/src/race.go:21 +0x6d

Goroutine 6 (running) created at:
  main.main()
      /root/gocode/src/race.go:20 +0x55
==================
19444
Found 1 data race(s)
exit status 66 
```

太棒了！`race detector`精准地发现了问题，而且还提供了如何修改的详细提示。添加写入`global`变量的锁：

```
package main

import (
    "fmt"
    "sync"
)

var global int
var wg sync.WaitGroup
var w sync.Mutex

func count() {
    defer wg.Done()
    for i := 0; i < 10000; i++{
        w.Lock()
        global++
        w.Unlock()
    }
}

func main() {
    wg.Add(2)
    go count()
    go count()
    wg.Wait()
    fmt.Println(global)
} 
```

这一次，竞争探测器保持平静：

```
# go run -race non_race.go
20000 
```

请习惯经常使用这个强大的工具，你会感激它的，我保证！

参考：

[介绍 Go 竞争探测器](https://blog.golang.org/race-detector)。
