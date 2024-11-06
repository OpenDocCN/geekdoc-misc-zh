# 切片的内部

# 切片的内部

* * *

切片有`3`个组成部分：

a) `指针`：指向底层数组中切片的起始位置；

b) `长度`（类型为`int`）：切片的有效元素数目；

b) `容量`（类型为`int`）：切片的总槽数。

检查以下代码：

```
package main

import (
    "fmt"
    "unsafe"
)

func main() {
    var s1 []int
    fmt.Println(unsafe.Sizeof(s1))
} 
```

在我的`64 位`系统上结果为`24`（`指针`和`int`都占据`8`个字节）。

在下一个示例中，我将使用`gdb`来查看切片的内部。 代码如下：

```
package main

import "fmt"

func main() {
        s1 := make([]int, 3, 5)
        copy(s1, []int{1, 2, 3})
        fmt.Println(len(s1), cap(s1), &s1[0])

        s1 = append(s1, 4)
        fmt.Println(len(s1), cap(s1), &s1[0])

        s2 := s1[1:]
        fmt.Println(len(s2), cap(s2), &s2[0])
} 
```

使用`gdb`进入代码：

```
5       func main() {
(gdb) n
6               s1 := make([]int, 3, 5)
(gdb)
7               copy(s1, []int{1, 2, 3})
(gdb)
8               fmt.Println(len(s1), cap(s1), &s1[0])
(gdb)
3 5 0xc820010240 
```

在执行"`s1 = append(s1, 4)`"之前，`fmt.Println`输出了切片的长度（`3`）、容量（`5`）和起始元素地址（`0xc820010240`），让我们来检查`s1`的内存布局：

```
10              s1 = append(s1, 4)
(gdb) p &s1
$1 = (struct []int *) 0xc82003fe40
(gdb) x/24xb 0xc82003fe40
0xc82003fe40:   0x40    0x02    0x01    0x20    0xc8    0x00    0x00    0x00
0xc82003fe48:   0x03    0x00    0x00    0x00    0x00    0x00    0x00    0x00
0xc82003fe50:   0x05    0x00    0x00    0x00    0x00    0x00    0x00    0x00
(gdb) 
```

通过检查内存内容`s1`（起始内存地址为`0xc82003fe40`），我们可以看到其内容与`fmt.Println`的输出匹配。

继续执行，并在"`s2 := s1[1:]`"之前检查结果：

```
(gdb) n
11              fmt.Println(len(s1), cap(s1), &s1[0])
(gdb)
4 5 0xc820010240
13              s2 := s1[1:]
(gdb) x/24xb 0xc82003fe40
0xc82003fe40:   0x40    0x02    0x01    0x20    0xc8    0x00    0x00    0x00
0xc82003fe48:   0x04    0x00    0x00    0x00    0x00    0x00    0x00    0x00
0xc82003fe50:   0x05    0x00    0x00    0x00    0x00    0x00    0x00    0x00 
```

我们可以看到在追加新元素（`s1 = append(s1, 4)`）后，`s1`的长度更改为`4`，但容量保持原始值。

让我们来检查`s2`的内部：

```
(gdb) n
14              fmt.Println(len(s2), cap(s2), &s2[0])
(gdb)
3 4 0xc820010248
15      }
(gdb) p &s2
$3 = (struct []int *) 0xc82003fe28
(gdb) x/24hb 0xc82003fe28
0xc82003fe28:   0x48    0x02    0x01    0x20    0xc8    0x00    0x00    0x00
0xc82003fe30:   0x03    0x00    0x00    0x00    0x00    0x00    0x00    0x00
0xc82003fe38:   0x04    0x00    0x00    0x00    0x00    0x00    0x00    0x00 
```

`s2`的元素起始地址是`0xc820010248`，实际上是`s1`的第二个元素（`0xc82003fe40`），长度（`3`）和容量（`4`）都比`s1`的对应值小一个（分别为`4`和`5`）。
