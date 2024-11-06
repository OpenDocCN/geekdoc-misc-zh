# copy

# copy

* * *

内置`copy`函数的定义在[这里](https://golang.org/pkg/builtin/#copy)：

> func copy(dst, src []Type) int
> 
> `copy`内置函数将元素从源片复制到目标片。（作为特例，它还会将字符串的字节复制到字节片中。）源片和目标片可能重叠。`copy`返回复制的元素数量，这将是`len(src)`和`len(dst)`的最小值。

让我们看一个基本示例，其中源片和目标片不重叠：

```
package main

import (
    "fmt"
)

func main() {
    d := make([]int, 3, 5)
    s := []int{2, 2}
    fmt.Println("Before copying (destination slice): ", d)
    fmt.Println("Copy length is: ", copy(d, s))
    fmt.Println("After copying (destination slice): ", d)

    d = make([]int, 3, 5)
    s = []int{2, 2, 2}
    fmt.Println("Before copying (destination slice): ", d)
    fmt.Println("Copy length is: ", copy(d, s))
    fmt.Println("After copying (destination slice): ", d)

    d = make([]int, 3, 5)
    s = []int{2, 2, 2, 2}
    fmt.Println("Before copying (destination slice): ", d)
    fmt.Println("Copy length is: ", copy(d, s))
    fmt.Println("After copying (destination slice): ", d)

} 
```

在上面的示例中，目标片的长度为`3`，源片的长度可以是`2`、`3`、`4`。检查结果：

```
Before copying (destination slice):  [0 0 0]
Copy length is:  2
After copying (destination slice):  [2 2 0]
Before copying (destination slice):  [0 0 0]
Copy length is:  3
After copying (destination slice):  [2 2 2]
Before copying (destination slice):  [0 0 0]
Copy length is:  3
After copying (destination slice):  [2 2 2] 
```

我们可以确保复制的元素数量确实是源片和目标片长度的最小值。

让我们检查重叠的情况：

```
package main

import (
    "fmt"
)

func main() {
    d := []int{1, 2, 3}
    s := d[1:]

    fmt.Println("Before copying: ", "source is: ", s, "destination is: ", d)
    fmt.Println(copy(d, s))
    fmt.Println("After copying: ", "source is: ", s, "destination is: ", d)

    s = []int{1, 2, 3}
    d = s[1:]

    fmt.Println("Before copying: ", "source is: ", s, "destination is: ", d)
    fmt.Println(copy(d, s))
    fmt.Println("After copying: ", "source is: ", s, "destination is: ", d)
} 
```

结果如下：

```
Before copying:  source is:  [2 3] destination is:  [1 2 3]
2
After copying:  source is:  [3 3] destination is:  [2 3 3]
Before copying:  source is:  [1 2 3] destination is:  [2 3]
2
After copying:  source is:  [1 1 2] destination is:  [1 2] 
```

通过输出，我们可以看到无论源片是否在目标片之前，结果始终如预期。你可以这样想象实现方式：首先将数据从源片复制到临时位置，然后将元素从临时位置复制到目标片。

`copy`要求源片和目标片是相同类型，一个例外是源片是字符串而目标片是`[]byte`：

```
package main

import (
    "fmt"
)

func main() {
    d := make([]byte, 20, 30)
    fmt.Println(copy(d, "Hello, 中国"))
    fmt.Println(string(d))
} 
```

输出为：

```
13
Hello, 中国 
```

参考：

[重叠时`copy()`的行为](https://groups.google.com/forum/#!msg/Golang-Nuts/HI6RI18S8L0/v6xevVPeS9EJ)。
