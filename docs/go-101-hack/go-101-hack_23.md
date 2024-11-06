# 类型

# 类型

* * *

`Go`中的类型分为`2`类：命名和未命名。除了预声明类型（如`int`、`rune`等），你也可以自己定义命名类型。例如：

```
type mySlice []int 
```

未命名类型是由类型字面量定义的。即，`[]int`是一个未命名类型。

根据[Go 规范](https://golang.org/ref/spec#Types)，每种类型都有一个基础类型：

> 每种类型 T 都有一个基础类型：如果 T 是预声明的布尔、数值或字符串类型之一，或者是一个类型字面量，那么相应的基础类型就是 T 本身。否则，T 的基础类型是 T 在其类型声明中引用的类型的基础类型。

因此，在上面的示例中，命名类型`mySlice`和未命名类型`[]int`都有相同的基础类型：`[]int`。

`Go`对变量赋值有严格的规则。例如：

```
package main

import "fmt"

type mySlice1 []int
type mySlice2 []int

func main() {
    var s1 mySlice1
    var s2 mySlice2 = s1

    fmt.Println(s1, s2)
} 
```

编译将会报以下错误：

```
cannot use s1 (type mySlice1) as type mySlice2 in assignment 
```

尽管`s1`和`s2`的基础类型相同：`[]int`，但它们属于`2`个不同的命名类型（`mySlice1`和`mySlice2`），所以它们不能相互赋值。但如果你修改`s2`的类型为`[]int`，则编译将会通过：

```
package main

import "fmt"

type mySlice1 []int

func main() {
    var s1 mySlice1
    var s2 []int = s1

    fmt.Println(s1, s2)
} 
```

其中的魔法是[可赋值性](https://golang.org/ref/spec#Assignability)的一个规则：

> x 的类型 V 和 T 具有相同的基础类型，且 V 或 T 中至少有一个不是命名类型。

参考：

[Go 规范](https://golang.org/ref/spec#Types)；

[学习 Go - 类型](http://www.laktek.com/2012/01/27/learning-go-types/)；

[Golang 智力测验](https://twitter.com/davecheney/status/734646224696016901)。
