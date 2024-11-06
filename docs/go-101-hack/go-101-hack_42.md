# 处理 JSON 对象

# 处理 JSON 对象

* * *

[JSON](http://www.json.org/)是一种常用且强大的数据交换格式，`Go`提供了内置的[json](https://golang.org/pkg/encoding/json/)包来处理它。让我们看下面的示例：

```
package main

import (
    "encoding/json"
    "log"
    "fmt"
)

type People struct {
    Name string
    age int
    Career string `json:"career"`
    Married bool `json:",omitempty"`
}

func main()  {
    p := &People{
        Name: "Nan",
        age: 34,
        Career: "Engineer",
    }

    data, err := json.Marshal(p)
    if err != nil {
        log.Fatalf("JSON marshaling failed: %s", err)
    }
    fmt.Printf("%s\n", data)
} 
```

执行结果如下所示：

```
{"Name":"Nan","career":"Engineer"} 
```

[Marshal](https://golang.org/pkg/encoding/json/#Marshal)函数用于将接口序列化为`JSON`对象。在我们的示例中，它对`People`结构进行编码：

(1) `Name`成员按我们的期望进行编码：

```
"Name":"Nan" 
```

(2) `age`字段在哪里？我们在结果中找不到它。原因是只有结构体的导出成员才能被编码，这意味着只有首字母大写的名称才能被编码为`JSON`对象（在我们的示例中，应该使用`Age`而不是`age`）。

(3) `Career`字段的名称是`career`，而不是`Career`：

```
"career":"Engineer" 
```

由于以下标签：`json:"career"`，告诉`Marshal`函数在`JSON`对象中使用`career`。

(4) 尽管`Married`已经被导出，但在结果中我们也看不到它，这背后的魔法是`json:",omitempty"`标签告诉`Marshal`函数如果使用默认值则不需要对该成员进行编码。

还有另一个[Unmarshal](https://golang.org/pkg/encoding/json/#Unmarshal)函数，用于解析`JSON`对象。看下面的示例，它是基于上面的示例扩展的：

```
package main

import (
    "encoding/json"
    "log"
    "fmt"
)

type People struct {
    Name string
    age int
    Career string `json:"career"`
    Married bool `json:",omitempty"`
}

func main()  {
    var p People
    data, err := json.Marshal(&People{Name: "Nan", age: 34, Career: "Engineer", Married: true})

    if err != nil {
        log.Fatalf("JSON marshaling failed: %s", err)
    }

    err = json.Unmarshal(data, &p)
    if err != nil {
        log.Fatalf("JSON unmarshaling failed: %s", err)
    }

    fmt.Println(p)
} 
```

运行结果如下：

```
{Nan 0 Engineer true} 
```

我们可以看到`JSON`对象成功解码。

除了`Marshal`和`Unmarshal`函数外，`json`包还提供了[Encoder](https://golang.org/pkg/encoding/json/#Encoder)和[Decoder](https://golang.org/pkg/encoding/json/#Decoder)结构体，用于处理来自流的`JSON`对象。例如，处理`HTTP`的代码通常如下：

```
func postFunc(w http.ResponseWriter, r *http.Request) {
    ......

    if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
        http.Error(w, err.Error(), http.StatusBadRequest)
        return
    }

    ......
} 
```

由于这两种方法的机制相似，这里不必过多讨论`Encoder`和`Decoder`。

参考资料：

[Package json](https://golang.org/pkg/encoding/json/)；

[Go 语言编程](http://www.gopl.io/)。
