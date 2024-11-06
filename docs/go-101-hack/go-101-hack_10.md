# Prepend

# Prepend

* * *

`Go`有一个内置的[append](https://golang.org/pkg/builtin/#append)函数，可以在切片中添加元素：

```
func append(slice []Type, elems ...Type) []Type 
```

但是如果我们想要实现"prepend"效果怎么办？也许我们应该使用`copy`函数。例如：

```
package main

import "fmt"

func main()  {
    var s []int = []int{1, 2}
    fmt.Println(s)

    s1 := make([]int, len(s) + 1)
    s1[0] = 0
    copy(s1[1:], s)
    s = s1
    fmt.Println(s)

} 
```

结果如下所示：

```
[1 2]
[0 1 2] 
```

但是上面的代码看起来又丑又繁琐，所以一个优雅的实现可能在这里：

```
s = append([]int{0}, s...) 
```

顺便说一句，我也尝试编写了一个"通用"的 prepend：

```
func Prepend(v interface{}, slice []interface{}) []interface{}{
    return append([]interface{}{v}, slice...)
} 
```

但是由于`[]T`不能直接转换为`[]interface{}`（请参考[`golang.org/doc/faq#convert_slice_of_interface`](https://golang.org/doc/faq#convert_slice_of_interface)，这只是一个玩具，没有实际用处。

参考：

[Go – 将项目追加/前置到切片中](https://codingair.wordpress.com/2014/07/18/go-appendprepend-item-into-slice/)。
