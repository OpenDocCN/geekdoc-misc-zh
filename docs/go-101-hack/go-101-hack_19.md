# 访问映射

# 访问映射

* * *

映射是一个指向哈希表的引用类型，你可以用它来构建一个非常方便的“键值”数据库，实际编程中非常有用。例如，以下代码将计算切片中每个元素的计数：

```
package main

import (
    "fmt"
)

func main() {
    s := []int{1, 1, 2, 2, 3, 3, 3}
    m := make(map[int]int)

    for _, v := range s {
        m[v]++
    }

    for key, value := range m {
        fmt.Printf("%d occurs %d times\n", key, value)
    }
} 
```

输出如下：

```
3 occurs 3 times
1 occurs 2 times
2 occurs 2 times 
```

此外，根据[Go 规范](https://golang.org/ref/spec#Map_types)："映射是一组**无序**的元素，类型相同，称为元素类型，由另一种类型的一组唯一键索引，称为键类型"。所以，如果你再次运行上述程序，输出可能会不同：

```
2 occurs 2 times
3 occurs 3 times
1 occurs 2 times 
```

你不能假设映射的元素顺序。

映射的键类型必须能够与“`==`”运算符进行比较：内置类型，如 int、string 等，满足此要求；而切片则不满足。对于结构体类型，如果它的成员都可以通过“`==`”运算符进行比较，则此结构体也可以用作键。

当你访问映射中不存在的键时，映射将返回元素的`nil`值。即：

```
package main

import (
    "fmt"
)

func main() {
    m := make(map[int]bool)

    m[0] = false
    m[1] = true

    fmt.Println(m[0], m[1], m[2])
} 
```

输出如下：

```
false true false 
```

`m[0]`和`m[2]`的值都为`false`，所以你无法区分键是否真的存在于映射中。解决方法是使用“逗号 OK”方法：

```
value, ok := map[key] 
```

如果键存在，`ok`将为`true`；否则`ok`将为`false`。

有时，你可能不关心映射的值，只把映射当作一个集合来使用。在这种情况下，你可以将值类型声明为空结构体：`struct{}`。一个示例如下：

```
package main

import (
    "fmt"
)

func check(m map[int]struct{}, k int) {
    if _, ok := m[k]; ok {
        fmt.Printf("%d is a valid key\n", k)
    }
}
func main() {
    m := make(map[int]struct{})
    m[0] = struct{}{}
    m[1] = struct{}{}

    for  i := 0; i <=2; i++ {
        check(m, i)
    }
} 
```

输出如下：

```
0 is a valid key
1 is a valid key 
```

使用内置的`delete`函数，你可以删除映射中的条目，即使键不存在：

```
delete(map, key) 
```

参考资料：

[Effective Go](https://golang.org/doc/effective_go.html);

[Go 编程语言规范](https://golang.org/ref/spec);

[Go 编程语言](http://www.gopl.io/)。
