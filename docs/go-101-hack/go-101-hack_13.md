# 将切片作为函数参数传递

# 将切片作为函数参数传递

* * *

在 `Go` 中，函数参数是按值传递的。就使用切片作为函数参数而言，这意味着函数将获得切片的副本：一个指向底层数组起始地址的指针，以及切片的长度和容量。哦，天哪！既然你知道用于存储数据的内存的地址，你现在可以调整切片了。让我们看下面的例子：

```
package main

import (
    "fmt"
)

func modifyValue(s []int)  {
    s[1] = 3
    fmt.Printf("In modifyValue: s is %v\n", s)
}
func main() {
    s := []int{1, 2}
    fmt.Printf("In main, before modifyValue: s is %v\n", s)
    modifyValue(s)
    fmt.Printf("In main, after modifyValue: s is %v\n", s)
} 
```

结果在这里：

```
In main, before modifyValue: s is [1 2]
In modifyValue: s is [1 3]
In main, after modifyValue: s is [1 3] 
```

你可以看到，运行 `modifyValue` 函数后，切片 `s` 的内容发生了变化。尽管 `modifyValue` 函数只是得到切片底层数组的内存地址的副本，但已经足够了！

再看另一个例子：

```
package main

import (
    "fmt"
)

func addValue(s []int) {
    s = append(s, 3)
    fmt.Printf("In addValue: s is %v\n", s)
}

func main() {
    s := []int{1, 2}
    fmt.Printf("In main, before addValue: s is %v\n", s)
    addValue(s)
    fmt.Printf("In main, after addValue: s is %v\n", s)
} 
```

结果如下：

```
In main, before addValue: s is [1 2]
In addValue: s is [1 2 3]
In main, after addValue: s is [1 2] 
```

这次，`addValue` 函数对 `main` 函数中的 `s` 切片没有产生影响。这是因为它只是操作 `s` 的副本，而不是“真正的” `s`。

所以，如果你真的想让函数改变切片的内容，你可以传递切片的地址：

```
package main

import (
    "fmt"
)

func addValue(s *[]int) {
    *s = append(*s, 3)
    fmt.Printf("In addValue: s is %v\n", s)
}

func main() {
    s := []int{1, 2}
    fmt.Printf("In main, before addValue: s is %v\n", s)
    addValue(&s)
    fmt.Printf("In main, after addValue: s is %v\n", s)
} 
```

结果如下：

```
In main, before addValue: s is [1 2]
In addValue: s is &[1 2 3]
In main, after addValue: s is [1 2 3] 
```
