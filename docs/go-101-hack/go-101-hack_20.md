# `switch`

# `switch`

* * *

相对于其他编程语言（比如`C`），`Go`的`switch-case`语句不需要显式的"`break`"，也没有`fall-though`特性。以以下代码为例：

```
package main

import (
    "fmt"
)

func checkSwitch(val int) {
    switch val {
    case 0:
    case 1:
        fmt.Println("The value is: ", val)
    }
}
func main() {
    checkSwitch(0)
    checkSwitch(1)
} 
```

输出为：

```
The value is:  1 
```

你的真实意图是 "`fmt.Println("The value is: ", val)`" 在`val`为`0`或`1`时执行，但实际上，该语句仅在`val`为`1`时生效。要满足你的要求，有`2`种方法：

(1) 使用`fallthrough`：

```
func checkSwitch(val int) {
    switch val {
    case 0:
        fallthrough
    case 1:
        fmt.Println("The value is: ", val)
    }
} 
```

(2) 将`0`和`1`放在同一个`case`中：

```
func checkSwitch(val int) {
    switch val {
    case 0, 1:
        fmt.Println("The value is: ", val)
    }
} 
```

`switch`也可以作为更好的`if-else`使用，你可能会发现它可能比多个`if-else`语句更清晰、更简单。例如：

```
package main

import (
    "fmt"
)

func checkSwitch(val int) {
    switch {
    case val < 0:
        fmt.Println("The value is less than zero.")
    case val == 0:
        fmt.Println("The value is qual to zero.")
    case val > 0:
        fmt.Println("The value is more than zero.")
    }
}
func main() {
    checkSwitch(-1)
    checkSwitch(0)
    checkSwitch(1)
} 
```

输出为：

```
The value is less than zero.
The value is qual to zero.
The value is more than zero. 
```
