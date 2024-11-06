# 数组

# 数组

* * *

在`Go`中，长度也是数组类型的一部分。因此，以下代码声明了一个数组：

```
var array [3]int 
```

当"`var slice []int`"定义一个切片时。由于这个特性，具有相同数组元素类型但不同长度的数组不能相互赋值。即：

```
package main

import "fmt"

func main() {
    var a1 [2]int
    var a2 [3]int
    a2 = a1
    fmt.Println(a2)
} 
```

编译器会报错：

```
cannot use a1 (type [2]int) as type [3]int in assignment 
```

将"`var a1 [2]int`"改为"`var a1 [3]int`"就可以使其正常工作。

另一个你应该注意的警告是以下代码声明了一个数组，而不是切片：

```
array := [...]int {1, 2, 3} 
```

你可以通过以下代码进行验证：

```
package main

import (
    "fmt"
    "reflect"
)

func main() {
    array := [...]int {1, 2, 3}
    slice := []int{1, 2, 3}
    fmt.Println(reflect.TypeOf(array), reflect.TypeOf(slice))
} 
```

输出为：

```
[3]int []int 
```

另外，在`Go`中，函数参数是按“值”传递的，所以如果你将数组作为函数参数使用，函数只会对原始副本进行操作。查看以下代码：

```
package main

import (
    "fmt"
)

func changeArray(array [3]int) {
    for i, _ := range array {
        array[i] = 1
    }
    fmt.Printf("In changeArray function, array address is %p, value is %v\n", &array, array)
}

func main() {
    var array [3]int

    fmt.Printf("Original array address is %p, value is %v\n", &array, array)
    changeArray(array)
    fmt.Printf("Changed array address is %p, value is %v\n", &array, array)
} 
```

输出为：

```
Original array address is 0xc082008680, value is [0 0 0]
In changeArray function, array address is 0xc082008700, value is [1 1 1]
Changed array address is 0xc082008680, value is [0 0 0] 
```

从日志中可以看到，在`changeArray`函数中数组的地址与`main`函数中数组的地址不同，因此原始数组的内容肯定不会被修改。此外，如果数组非常大，在将参数传递给函数时复制它们可能会产生比你想要的更多的开销，你应该知道这一点。
