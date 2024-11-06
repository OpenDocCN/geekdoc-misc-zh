# defer

# defer

* * *

`defer`语句用于延迟在周围函数返回之前立即执行的函数调用。`defer`的常见用途包括释放资源（例如解锁互斥锁，关闭文件句柄），进行一些跟踪（例如记录函数的运行时间）等。例如，一个普通的独占访问全局变量的方式如下：

```
var mu sync.Mutex
var m = make(map[string]int)

func lookup(key string) int {
    mu.Lock()
    v := m[key]
    mu.Unlock()
    return v
} 
```

使用`defer`的等效但更简洁的格式如下：

```
var mu sync.Mutex
var m = make(map[string]int)

func lookup(key string) int {
    mu.Lock()
    defer mu.Unlock()
    return m[key]
} 
```

你可以看到这种风格更简单、更易于理解。

`defer`语句按照后进先出的顺序执行，这意味着后面的`defer`语句中的函数会在前面的函数之前运行。请查看以下示例：

```
package main

import "fmt"

func main()  {
    defer fmt.Println("First")
    defer fmt.Println("Last")
} 
```

运行结果如下：

```
Last
First 
```

尽管`defer`语句中的函数运行得很晚，但函数的参数在执行`defer`语句时就会被评估。

```
package main

import "fmt"

func main()  {
    i := 10
    defer fmt.Println(i)
    i = 100
} 
```

运行结果如下：

```
10 
```

此外，如果延迟执行的函数是函数文字，它也可以修改返回值：

```
package main

import "fmt"

func modify() (result int) {
    defer func(){result = 1000}()
    return 100
}

func main()  {
    fmt.Println(modify())
} 
```

打印的值是`1000`，而不是`100`。

参考资料：

[Go 编程语言](http://www.gopl.io/)；

[延迟、恐慌和恢复](https://blog.golang.org/defer-panic-and-recover)。
