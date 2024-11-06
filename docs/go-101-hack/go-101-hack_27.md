# io.Writer 接口

## io.Writer 接口

[io.Reader](https://golang.org/pkg/io/#Reader) 的逆接口是 [io.Writer](https://golang.org/pkg/io/#Writer) 接口：

```
type Writer interface {
        Write(p []byte) (n int, err error)
} 
```

与`io.Reader`相比，由于不需要考虑`io.EOF`错误，`Write`方法的过程很简单：

(1) `err == nil`：`p`中的所有数据均成功写入；

(2) `err != nil`：`p`中的数据部分或全部未写入。

让我们看一个例子：

```
package main

import (
        "log"
        "os"
)

func main() {
        f, err := os.Create("test.txt")
        if err != nil {
                log.Fatal(err)
        }
        defer f.Close()

        if _, err = f.Write([]byte{'H', 'E', 'L', 'L', 'O'}); err != nil {
                log.Fatal(err)
        }
} 
```

在执行程序后，将创建`test.txt`：

```
# cat test.txt
HELLO 
```
