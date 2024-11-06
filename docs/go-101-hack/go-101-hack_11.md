# 字符串

# 字符串

* * *

在`Go`中，字符串是一个不可变的字节数组。所以如果创建了，我们无法更改它的值。例如：

```
package main

func main()  {
    s := "Hello"
    s[0] = 'h'
} 
```

编译器会抱怨：

```
cannot assign to s[0] 
```

要修改字符串的内容，你可以将其转换为`byte`数组。但实际上，你**并不会**操作原始字符串，只是一个副本：

```
package main

import "fmt"

func main()  {
    s := "Hello"
    b := []byte(s)
    b[0] = 'h'
    fmt.Printf("%s\n", b)
} 
```

结果是这样的：

```
hello 
```

由于`Go`使用`UTF-8`编码，你必须记住`len`函数将返回字符串的字节数，而不是字符数：

```
package main

import "fmt"

func main()  {
    s := "日志 log"
    fmt.Println(len(s))
} 
```

结果是：

```
9 
```

因为每个中文字符占用`3`个字节，上述例子中的`s`包含`5`个字符和`9`个字节。

如果你想访问每个字符，`for ... range`循环可以提供帮助：

```
package main
import "fmt"

func main() {
    s := "日志 log"
    for index, runeValue := range s {
        fmt.Printf("%#U starts at byte position %d\n", runeValue, index)
    }
} 
```

结果是：

```
U+65E5 '日' starts at byte position 0
U+5FD7 '志' starts at byte position 3
U+006C 'l' starts at byte position 6
U+006F 'o' starts at byte position 7
U+0067 'g' starts at byte position 8 
```

参考：

[Go 中的字符串、字节、符文和字符](https://blog.golang.org/strings)；

[Go 语言程序设计](http://www.gopl.io/)。
