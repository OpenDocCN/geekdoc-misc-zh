# io.Reader 接口

## io.Reader 接口

`io.Reader`接口是一个基本且非常常用的接口：

```
type Reader interface {
        Read(p []byte) (n int, err error)
} 
```

对于每种满足`io.Reader`接口的类型，你可以想象它是一个管道。有人向管道的一端写入内容，你可以使用类型提供的`Read()`方法从管道的另一端读取内容。无论是普通文件、网络套接字等等。只要兼容`io.Reader`接口，我就可以读取它的内容。

让我们看一个例子：

```
package main

import (
    "fmt"
    "io"
    "log"
    "os"
)

func main() {
    file, err := os.Open("test.txt")
    if err != nil {
        log.Fatal(err)
    }
    defer file.Close()

    p := make([]byte, 4)
    for {
        if n, err := file.Read(p); n > 0 {
            fmt.Printf("Read %s\n", p[:n])
        } else if err != nil {
            if err == io.EOF {
                fmt.Println("Read all of the content.")
                break
            } else {
                log.Fatal(err)
            }
        } else /* n == 0 && err == nil */ {
            /* do nothing */
        }
    }
} 
```

在发出`read()`调用后，可以看到有`3`种情况需要考虑：

(1) `n > 0`：读取有效内容；处理它；

(2) `n == 0 && err != nil`：如果`err`是`io.EOF`，表示所有内容都已经被读取，没有剩余内容；否则发生了意外情况，需要进行特殊操作；

(3) `n == 0 && err == nil`：根据[io 包文档](https://golang.org/pkg/io/#Reader)，表示没有发生任何事情，因此不需要做任何操作。

创建一个只包含`5`字节的`test.txt`文件：

```
# cat test.txt
abcde 
```

执行程序，结果如下：

```
Read abcd
Read e
Read all of the content. 
```

参考：

[io 包文档](https://golang.org/pkg/io/#Reader)。
