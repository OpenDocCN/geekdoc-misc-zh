# 重新分配切片的底层数组

# 重新分配切片的底层数组

* * *

当向切片中添加数据时，如果切片的底层数组没有足够的空间，将会分配一个新的数组。然后将旧数组中的元素复制到这个新的内存中，并在后面添加新的数据。因此，在使用`Go`内置的`append`函数时，你必须始终牢记“数组可能已经被修改”的想法，并且要非常小心，否则它可能会伤害到你！

让我通过一个刻意制造的例子来解释：

```
package main

import (
    "fmt"
)

func addTail(s []int)  {
    var ns [][]int
    for _, v := range []int{1, 2} {
        ns = append(ns, append(s, v))
    }
    fmt.Println(ns)
}

func main() {
    s1 := []int{0, 0}
    s2 := append(s1, 0)

    for _, v := range [][]int{s1, s2} {
        addTail(v)
    }
} 
```

`s1`是`[0, 0]`，而`s2`是`[0, 0, 0]`；在`addTail`函数中，我想在切片后面添加`1`和`2`。所以期望的输出应该是这样的：

```
[[0 0 1] [0 0 2]]
[[0 0 0 1] [0 0 0 2]] 
```

但实际结果是：

```
[[0 0 1] [0 0 2]]
[[0 0 0 2] [0 0 0 2]] 
```

对`s1`的操作成功，而`s2`没有成功。

让我们使用`delve`来调试这个问题，并检查切片的内部机制：在`addTail`函数上设置断点，当处理`s1`时首先命中：

```
(dlv) n
> main.addTail() ./slice.go:8 (PC: 0x401022)
     3: import (
     4:         "fmt"
     5: )
     6:
     7: func addTail(s []int)  {
=>   8:         var ns [][]int
     9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
    12:         fmt.Println(ns)
    13: }
(dlv) p s
[]int len: 2, cap: 2, [0,0]
(dlv) p &s[0]
(*int)(0xc82000a2a0) 
```

`s1`的长度和容量都是`2`，底层数组的地址是`0xc82000a2a0`，所以在执行以下语句时会发生什么：

```
ns = append(ns, append(s, v)) 
```

由于`s1`的长度和容量都是`2`，没有足够的空间添加新元素。要添加一个新值，必须分配一个新的数组，其中包含来自`s1`的`[0, 0]`和新值（`1`或`2`）。你可以将`append(s, v)`看作生成了一个匿名的新切片，并且它被附加在`ns`中。我们可以在运行"`ns = append(ns, append(s, v))`"后检查它：

```
(dlv) n
> main.addTail() ./slice.go:9 (PC: 0x401217)
     4:         "fmt"
     5: )
     6:
     7: func addTail(s []int)  {
     8:         var ns [][]int
=>   9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
    12:         fmt.Println(ns)
    13: }
    14:
(dlv) p ns
[][]int len: 1, cap: 1, [
        [0,0,1],
]
(dlv) p ns[0]
[]int len: 3, cap: 4, [0,0,1]
(dlv) p &ns[0][0]
(*int)(0xc82000e240)
(dlv) p s
[]int len: 2, cap: 2, [0,0]
(dlv) p &s[0]
(*int)(0xc82000a2a0) 
```

我们可以看到匿名切片的长度为`3`，容量为`4`，底层数组地址为`0xc82000e240`，与`s1`的地址（`0xc82000a2a0`）不同。继续执行直到退出循环：

```
(dlv) n
> main.addTail() ./slice.go:12 (PC: 0x40124c)
     7: func addTail(s []int)  {
     8:         var ns [][]int
     9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
=>  12:         fmt.Println(ns)
    13: }
    14:
    15: func main() {
    16:         s1 := []int{0, 0}
    17:         s2 := append(s1, 0)
(dlv) p ns
[][]int len: 2, cap: 2, [
        [0,0,1],
        [0,0,2],
]
(dlv) p &ns[0][0]
(*int)(0xc82000e240)
(dlv) p &ns[1][0]
(*int)(0xc82000e280)
(dlv) p &s[0]
(*int)(0xc82000a2a0) 
```

我们可以看到`s1`、`ns[0]`和`ns[1]`有`3`个独立的数组。

现在，让我们按照相同的步骤来检查`s2`上发生了什么：

```
(dlv) n
> main.addTail() ./slice.go:8 (PC: 0x401022)
     3: import (
     4:         "fmt"
     5: )
     6:
     7: func addTail(s []int)  {
=>   8:         var ns [][]int
     9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
    12:         fmt.Println(ns)
    13: }
(dlv) p s
[]int len: 3, cap: 4, [0,0,0]
(dlv) p &s[0]
(*int)(0xc82000e220) 
```

`s2`的长度是`3`，容量是`4`，因此有一个位置可以添加新元素。在第一次执行"`ns = append(ns, append(s, v))`"后，检查`ns`和`ns`的值：

```
(dlv)
> main.addTail() ./slice.go:9 (PC: 0x401217)
     4:         "fmt"
     5: )
     6:
     7: func addTail(s []int)  {
     8:         var ns [][]int
=>   9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
    12:         fmt.Println(ns)
    13: }
    14:
(dlv) p ns
[][]int len: 1, cap: 1, [
        [0,0,0,1],
]
(dlv) p &ns[0][0]
(*int)(0xc82000e220)
(dlv) p s
[]int len: 3, cap: 4, [0,0,0]
(dlv) p &s[0]
(*int)(0xc82000e220) 
```

我们可以看到新匿名切片的数组地址也是`0xc82000e220`，这是因为`s2`有足够的空间来容纳新值，不需要分配新数组。再次在添加`2`后检查`s2`和`ns`：

```
(dlv)
> main.addTail() ./slice.go:12 (PC: 0x40124c)
     7: func addTail(s []int)  {
     8:         var ns [][]int
     9:         for _, v := range []int{1, 2} {
    10:                 ns = append(ns, append(s, v))
    11:         }
=>  12:         fmt.Println(ns)
    13: }
    14:
    15: func main() {
    16:         s1 := []int{0, 0}
    17:         s2 := append(s1, 0)
(dlv) p ns
[][]int len: 2, cap: 2, [
        [0,0,0,2],
        [0,0,0,2],
]
(dlv) p &ns[0][0]
(*int)(0xc82000e220)
(dlv) p &ns[1][0]
(*int)(0xc82000e220)
(dlv) p s
[]int len: 3, cap: 4, [0,0,0]
(dlv) p &s[0]
(*int)(0xc82000e220) 
```

所有`3`个切片指向同一个数组，因此后面的值（`2`）将覆盖前面的项（`1`）。

因此，总的来说，`append`非常棘手，因为它可以在不知情的情况下修改底层数组。你必须清楚地了解每个切片背后的内存布局，否则切片可能会给你一个巨大的、意想不到的惊喜！
