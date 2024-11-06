# 缓冲读取

## 缓冲读取

[bufio](https://golang.org/pkg/bufio/)包提供了缓冲读取函数。让我们看一个例子：

(1) 首先创建一个`test.txt`文件：

```
# cat test.txt
abcd
efg
hijk
lmn 
```

你可以看到`test.txt`包含`4`行。

(2) 查看以下程序：

```
package main

import (
        "bufio"
        "fmt"
        "io"
        "log"
        "os"
)

func main() {
        f, err := os.Open("test.txt")
        if err != nil {
                log.Fatal(err)
        }

        r := bufio.NewReader(f)
        for {
                if s, err := r.ReadSlice('\n'); err == nil || err == io.EOF {
                        fmt.Printf("%s", s)
                        if err == io.EOF {
                                break
                        }
                } else {
                        log.Fatal(err)
                }

        }
} 
```

(a)

```
f, err := os.Open("test.txt") 
```

打开`test.txt`文件。

(b)

```
r := bufio.NewReader(f) 
```

`bufio.NewReader(f)`创建一个[bufio.Reader](https://golang.org/pkg/bufio/#Reader)结构，实现了缓冲读取功能。

(c)

```
for {
    if s, err := r.ReadSlice('\n'); err == nil || err == io.EOF {
        fmt.Printf("%s", s)
        if err == io.EOF {
            break
        }
    } else {
        log.Fatal(err)
    }

} 
```

读取并打印每一行。

运行结果在这里：

```
abcd
efg
hijk
lmn 
```

我们还可以使用[bufio.Scanner](https://golang.org/pkg/bufio/#Scanner)来实现上述的"打印每一行"功能：

```
package main

import (
        "bufio"
        "fmt"
        "log"
        "os"
)

func main() {
        f, err := os.Open("test.txt")
        if err != nil {
                log.Fatal(err)
        }

        s := bufio.NewScanner(f)

        for s.Scan() {
                fmt.Println(s.Text())
        }
} 
```

(a)

```
s := bufio.NewScanner(f) 
```

`bufio.NewScanner(f)`创建一个新的[bufio.Scanner](https://golang.org/pkg/bufio/#Scanner)结构，默认按行分隔内容。

(b)

```
for s.Scan() {
    fmt.Println(s.Text())
} 
```

`s.Scan()`将`bufio.Scanner`推进到下一个标记（在本例中，是一个可选的回车符后跟一个必需的换行符），我们可以使用`s.Text()`函数获取内容。

我们还可以自定义[SplitFunc](https://golang.org/pkg/bufio/#SplitFunc)函数，它不会按行分隔内容。查看以下代码：

```
package main

import (
        "bufio"
        "fmt"
        "log"
        "os"
)

func main() {
        f, err := os.Open("test.txt")
        if err != nil {
                log.Fatal(err)
        }

        s := bufio.NewScanner(f)
        split := func(data []byte, atEOF bool) (advance int, token []byte, err error) {
                for i := 0; i < len(data); i++ {
                        if data[i] == 'h' {
                                return i + 1, data[:i], nil
                        }
                }

                return 0, data, bufio.ErrFinalToken
        }
        s.Split(split)
        for s.Scan() {
                fmt.Println(s.Text())
        }
} 
```

`split`函数通过"`h`"分隔内容，运行结果是：

```
abcd
efg

ijk
lmn 
```
