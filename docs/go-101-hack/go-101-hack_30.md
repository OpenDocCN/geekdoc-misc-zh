# 范围

## 范围

`for ... range` 子句可用于迭代 `5` 种类型的变量：数组、切片、字符串、映射和通道，以下表格总结了 `for ... range` 循环的项目：

| 类型 | 第一项 | 第二项 |
| --- | --- | --- |
| 数组 | 索引 | 值 |
| 切片 | 索引 | 值 |
| 字符串 | 索引（rune） | 值（rune） |
| 映射 | 键 | 值 |
| 通道 | 值 |  |

对于数组、切片、字符串和映射，如果不关心第二项，可以省略它。例如：

```
package main

import "fmt"

func main() {
    m := map[string]struct{} {
        "alpha": struct{}{},
        "beta": struct{}{},
    }
    for k := range m {
        fmt.Println(k)
    }
} 
```

运行结果如下所示：

```
alpha
beta 
```

同样，如果程序不需要第一项，应该使用空白标识符占据该位置：

```
package main

import "fmt"

func main() {
    for _, v := range []int{1, 2, 3} {
        fmt.Println(v)
    }
} 
```

输出为：

```
1
2
3 
```

对于通道类型，`close` 操作可能导致 `for ... range` 循环退出。参见以下代码：

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

检查结果：

```
1
2
The channel is closed. 
```

我们可以看到另一个 goroutine 中的 `close(ch)` 语句使主 goroutine 中的循环结束。
