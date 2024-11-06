# 优先选择领域特定的类型而不是原始类型

# 优先选择领域特定的类型而不是原始类型

1999 年 9 月 23 日，价值$327.6 百万的火星气候轨道飞行器在进入火星轨道时由于地球上的软件错误而丢失。这个错误后来被称为*度量混乱*。地面站软件使用英镑而飞船期望使用牛顿，导致地面站低估了飞船推进器的功率约 4.45 倍。

这是许多软件故障的例子之一，如果应用了更强大和更具领域特定的类型系统，则可以预防。这也是 Ada 语言中许多特性背后的理由之一，该语言的主要设计目标之一是实现嵌入式安全关键软件。Ada 具有对基本类型和用户定义类型进行静态检查的强类型：

```
type Velocity_In_Knots is new Float range 0.0 .. 500.00;

type Distance_In_Nautical_Miles is new Float range 0.0 .. 3000.00;

Velocity: Velocity_In_Knots;

Distance: Distance_In_Nautical_Miles;

Some_Number: Float;

Some_Number:= Distance + Velocity; -- Will be caught by the compiler as a type error. 
```

在需求较低的领域开发者也可能受益于应用更多领域特定的类型，否则他们可能会继续使用语言及其库提供的原始数据类型，如字符串和浮点数。在 Java、C++、Python 和其他现代语言中，抽象数据类型被称为类。使用诸如`Velocity_In_Knots`和`Distance_In_Nautical_Miles`等类，对于代码质量具有很大的价值：

1.  代码更易读，因为它表达了领域的概念，而不仅仅是 Float 或 String。

1.  代码封装了易于测试的行为，使得代码更具有可测试性。

1.  代码促进了跨应用程序和系统的重用。

这种方法对于静态类型语言和动态类型语言的用户同样有效。唯一的区别在于，使用静态类型语言的开发者会得到编译器的一些帮助，而那些接受动态类型语言的开发者更可能依赖他们的单元测试。检查的风格可能不同，但动机和表达的风格是一致的。

教训是开始探索领域特定的类型，以开发高质量的软件。

作者：[Einar Landre](http://programmer.97things.oreilly.com/wiki/index.php/Einar_Landre)
