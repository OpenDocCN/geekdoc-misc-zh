# “nil 切片” vs “nil 映射”

# “nil 切片” vs “nil 映射”

* * *

在`Go`中，切片和映射都是引用类型，它们的默认值是`nil`：

```
package main

import "fmt"

func main() {
    var (
        s []int
        m map[int]bool
    )
    if s == nil {
        fmt.Println("The value of s is nil")
    }
    if m == nil {
        fmt.Println("The value of m is nil")
    }
} 
```

结果如下：

```
The value of s is nil
The value of m is nil 
```

当切片的值为`nil`时，你也可以对其进行操作，比如`append`：

```
package main

import "fmt"

func main() {
    var s []int
    fmt.Println("Is s a nil? ", s == nil)
    s = append(s, 1)
    fmt.Println("Is s a nil? ", s == nil)
    fmt.Println(s)
} 
```

结果如下：

```
Is s a nil?  true
Is s a nil?  false
[1] 
```

你应该注意的一个警告是`nil`和空切片的长度都是`0`：

```
package main

import "fmt"

func main() {
    var s1 []int
    s2 := []int{}
    fmt.Println("Is s1 a nil? ", s1 == nil)
    fmt.Println("Length of s1 is: ", len(s1))
    fmt.Println("Is s2 a nil? ", s2 == nil)
    fmt.Println("Length of s2 is: ", len(s2))
} 
```

结果如下：

```
Is s1 a nil?  true
Length of s1 is:  0
Is s2 a nil?  false
Length of s2 is:  0 
```

所以你应该将切片的值与`nil`进行比较，以检查它是否为`nil`。

访问`nil`映射是可以的，但存储`nil`映射会导致程序崩溃：

```
package main

import "fmt"

func main() {
    var m map[int]bool
    fmt.Println("Is m a nil? ", m == nil)
    fmt.Println("m[1] is ", m[1])
    m[1] = true
} 
```

结果如下：

```
Is m a nil?  true
m[1] is  false
panic: assignment to entry in nil map

goroutine 1 [running]:
panic(0x4cc0e0, 0xc082034210)
    C:/Go/src/runtime/panic.go:481 +0x3f4
main.main()
    C:/Work/gocode/src/Hello.go:9 +0x2ee
exit status 2

Process finished with exit code 1 
```

所以最佳实践是在使用之前初始化一个`映射`，就像这样：

```
m := make(map[int]bool) 
```

顺便说一句，你应该使用以下模式来检查映射中是否存在元素：

```
if v, ok := m[1]; !ok {
    .....
} 
```

参考：

[《Go 编程语言》](http://www.gopl.io/)。
