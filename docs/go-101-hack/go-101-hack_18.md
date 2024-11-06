# 数组和切片之间的转换

## 数组和切片之间的转换

在`Go`中，数组是具有指定类型的固定长度连续内存，而切片只是一个指向底层数组的引用。由于它们是不同类型，不能直接互相赋值。请看下面的例子：

```
package main

import "fmt"

func main() {
    s := []int{1, 2, 3}
    var a [3]int

    fmt.Println(copy(a, s))
} 
```

因为`copy`只接受切片参数，我们可以使用`[:]`从数组创建一个切片。查看下面的代码：

```
package main

import "fmt"

func main() {
    s := []int{1, 2, 3}
    var a [3]int

    fmt.Println(copy(a[:2], s))
    fmt.Println(a)
} 
```

运行输出为：

```
2
[1 2 0] 
```

上面的例子是从切片复制值到数组，相反的操作类似：

```
package main

import "fmt"

func main() {
    a := [...]int{1, 2, 3}
    s := make([]int, 3)

    fmt.Println(copy(s, a[:2]))
    fmt.Println(s)
} 
```

执行结果为：

```
2
[1 2 0] 
```

参考资料：

[在 golang 中如何将切片转换为数组](http://stackoverflow.com/questions/19073769/in-golang-how-do-you-convert-a-slice-into-an-array);

[数组、切片（和字符串）：'append' 的机制](https://blog.golang.org/slices).
