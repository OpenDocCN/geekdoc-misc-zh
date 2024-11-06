# 通道类型

# 通道类型

* * *

在声明通道类型的变量时，最常见的实例如下（`T`是任何有效类型）：

```
var v chan T 
```

但你可能也会看到以下示例：

```
var v <-chan T 
```

或者：

```
var v chan<- T 
```

这`3`个定义之间到底有何区别？区别在于这里：

(1) `chan T`：通道可以接收和发送`T`类型的数据；

(2) `<-chan T`：通道是**只读**的，这意味着你只能从该通道**接收**`T`类型的数据；

(2) `chan<- T`：通道是**只写**的，这意味着你只能向该通道**发送**`T`类型的数据。

将助记符与通道操作相关联：

```
v := <-ch  // Receive from ch, and assign value to v.
ch <- v    // Send v to channel ch. 
```

`<-chan T`类似于`v := <-ch`，因此它是一个只接收的通道，与`chan<- T`和`ch <- v`相同。

限制通道类型（只读或只写）可以让编译器为你进行严格的检查。例如：

```
package main

func f() (<-chan int) {
    ch := make(chan int)
    return ch
}

func main()  {
    r := f()
    r <- 1
} 
```

编译生成以下错误：

```
invalid operation: r <- 1 (send to receive-only type <-chan int) 
```

此外，`<-`运算符与**最左侧**可能的`chan`相关联，即`chan<- chan int`和`chan (<-chan int)`并不相等：前者与`chan<- (chan int)`相同，它定义了一个数据类型为通道的**只写**通道，该通道可以接收和发送`int`数据；而`chan (<-chan int)`定义了一个数据类型为通道的**读写**通道，该通道只能接收`int`数据。

参考资料：

[通道类型](https://nanxiao.gitbooks.io/golang-101-hacks/content/posts/unbuffered-and-buffered-channels.html);

[如何理解声明中的"<-chan"？](https://groups.google.com/forum/#!topic/golang-nuts/ul_K7S3EtOk)。
