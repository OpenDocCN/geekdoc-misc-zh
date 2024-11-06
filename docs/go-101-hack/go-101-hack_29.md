# 排序

## 排序

`sort`包定义了一个名为`Interface`的[接口](https://golang.org/pkg/sort/#Interface)：

```
type Interface interface {  
        // Len is the number of elements in the collection.  
        Len() int  
        // Less reports whether the element with  
        // index i should sort before the element with index j.  
        Less(i, j int) bool  
        // Swap swaps the elements with indexes i and j.  
        Swap(i, j int)  
} 
```

对于切片，或者任何其他实现了`Len()`，`Less`和`Swap`函数的集合类型，你可以使用`sort.Sort()`函数按顺序排列元素。

让我们看下面的示例：

```
package main

import (
    "fmt"
    "sort"
)

type command struct  {
    name string
}

type byName []command

func (a byName) Len() int           { return len(a) }
func (a byName) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a byName) Less(i, j int) bool { return a[i].name < a[j].name }

func main() {
    c := []command{
        {"breakpoint"},
        {"help"},
        {"args"},
        {"continue"},
    }
    fmt.Println("Before sorting: ", c)
    sort.Sort(byName(c))
    fmt.Println("After sorting: ", c)
} 
```

为了不失焦点地展示如何使用`sort.Interface`，`command`结构被简化为只包含一个`string`成员：`name`。比较方法（`Less`）只是按字母顺序对比`name`。

检查程序的运行结果：

```
Before sorting:  [{breakpoint} {help} {args} {continue}]
After sorting:  [{args} {breakpoint} {continue} {help}] 
```

我们可以看到在排序后，`c`中的项目被重新排列了。

另外，如果你在意性能，你可以定义一个元素类型为指针的切片，因为如果元素的大小非常大，切换指针会快得多。修改上面的例子：

```
package main

import (
    "fmt"
    "sort"
)

type command struct  {
    name string
    help string
}

type byName []*command

func (a byName) Len() int           { return len(a) }
func (a byName) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a byName) Less(i, j int) bool { return a[i].name < a[j].name }

func main() {
    c := []*command{
        {"breakpoint", "Set breakpoints"},
        {"help", "Show help"},
        {"args", "Print arguments"},
        {"continue", "Continue"},
    }
    fmt.Println("Before sorting: ", c)
    sort.Sort(byName(c))
    fmt.Println("After sorting: ", c)
} 
```

检查执行结果：

```
Before sorting:  [0xc0820066a0 0xc0820066c0 0xc0820066e0 0xc082006700]
After sorting:  [0xc0820066e0 0xc0820066a0 0xc082006700 0xc0820066c0] 
```

你可以看到指针被重新排序了。

参考：

[《Go 编程语言》](http://www.gopl.io/)。
