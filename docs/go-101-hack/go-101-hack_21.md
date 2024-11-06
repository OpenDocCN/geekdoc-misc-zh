# 接口

## 接口

接口是一个引用类型，其中包含一些方法定义。任何实现了引用类型定义的所有方法的类型都会自动满足这个接口类型。通过接口，你可以使用面向对象编程。看下面的例子：

```
package main

import "fmt"

type Foo interface {
    foo()
}

type A struct {
}

func (a A) foo() {
    fmt.Println("A foo")
}

func (a A) bar() {
    fmt.Println("A bar")
}

func callFoo(f Foo) {
    f.foo()
}

func main() {
    var a A
    callFoo(a)
} 
```

运行结果是：

```
A foo 
```

让我们详细分析一下代码：

(1)

```
type Foo interface {
    foo()
} 
```

上面的代码定义了一个只有一个方法 `foo()` 的接口 `Foo`。

(2)

```
type A struct {
}

func (a A) foo() {
    fmt.Println("A foo")
}

func (a A) bar() {
    fmt.Println("A bar")
} 
```

结构体 `A` 有 `2` 个方法：`foo()` 和 `bar()`。由于它已经实现了 `foo()` 方法，所以它满足 `Foo` 接口。

(3)

```
func callFoo(f Foo) {
    f.foo()
}

func main() {
    var a A
    callFoo(a)
} 
```

`callFoo` 需要一个类型为 `Foo` 接口的变量，传递 `A` 是可以的。`callFoo` 将使用 `A` 的 `foo()` 方法，并打印出“`A foo`”。

让我们修改 `main()` 函数：

```
func main() {
    var a A
    callFoo(&a)
} 
```

这一次，`callFoo()` 的参数是 `&a`，它的类型是 `*A`。编译并运行程序，你可能会发现它也输出了：“`A foo`”。所以 `*A` 类型拥有 `A` 所有的方法。但反过来不成立：

```
package main

import "fmt"

type Foo interface {
    foo()
}

type A struct {
}

func (a *A) foo() {
    fmt.Println("A foo")
}

func (a *A) bar() {
    fmt.Println("A bar")
}

func callFoo(f Foo) {
    f.foo()
}

func main() {
    var a A
    callFoo(a)
} 
```

编译程序：

```
example.go:26: cannot use a (type A) as type Foo in argument to callFoo:
A does not implement Foo (foo method has pointer receiver) 
```

你还可以看到 `*A` 类型实现了 `foo()` 和 `bar()` 方法，这并不意味着 `A` 类型默认就有这两个方法。

顺便说一句，每种类型都满足空接口：`interface{}`。

接口类型实际上是一个包含 `2` 个元素的元组：`<type, value>`，`type` 标识存储在接口中的变量的类型，而 `value` 指向实际的值。接口类型的默认值是 `nil`，这意味着 `type` 和 `value` 都是 `nil`：`<nil, nil>`。当你检查一个接口是否为空时：

```
var err error
if err != nil {
    ...
} 
```

你必须记住，只有当 `type` 和 `value` 都是 `nil` 时，接口值才是 `nil`。

参考资料：

[Go 语言圣经](http://www.gopl.io/)。
