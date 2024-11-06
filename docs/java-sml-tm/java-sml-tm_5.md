# 糟糕的建议

# 糟糕的建议

一些真正糟糕的想法常被宣传为“最佳实践”。在这一节中，我们提供例子并解释为什么它们应该被忽略。

# 单一退出点规则

## 糟糕的建议 - 单一退出点规则

一些编码标准要求所有方法都应该有单一退出点。

这样做可能会有害，特别是当它被静态分析强制执行时。

## 细节

单一退出点是一个历史悠久的概念，可以追溯到自由使用 goto 和过时的编程风格时代。

在这种情况下，对函数内部可能发生的事情添加约束是有帮助的。知道一个大函数只有一个退出点，使得理解更加容易。

许多现代函数式语言继续要求或鼓励使用单一退出点。

所以，把这个约束条件添加到 Java 中一定是个好主意，对吗？

让我们看看当我们被告知只能有一个退出点时会发生什么：

**带语句的单一退出点**

```
public class Example {
  private int value;

  public int single(int x) {
    int retVal = 0;

    if (x == 10) {
      retVal = -value;
    } else if (x > 0) {
      retVal = value + x;
    }

    return retVal;
  }

} 
```

如果我们去除单一退出点的约束条件，我们会得到：

**多退出**

```
public class Example {
  private int value;

  public int multi(int x) {
    if (x == 10) {
      return -value;
    }

    if (x > 0) {
      return value + x;
    }

    return 0;
  }
} 
```

哪个版本更好？

两种方法差别不大，但是多退出点版本更容易理解。

试图应用单一退出点约束导致额外的本地变量用于保存返回状态。在多退出版本中，我们可以清楚地看到当条件都不匹配时返回了什么值。在单一退出版本中，情况略微不太清晰，因为返回的值在方法开始时被声明，然后被覆盖。

这意味着单一退出点方法是不好的吗？

不。

也可以编写替代的单一退出点实现。

```
 public int oneAssignment(int x) {
    final int retVal;

    if (x == 10) {
      retVal = -value;
    } else if (x > 0) {
      retVal = value + x;
    } else {
      retVal = 0;
    }

    return retVal;
  } 
```

我们解决了之前确定的问题。我们只对`retVal`赋值一次，并且清楚地知道在条件都不匹配时赋予了什么值。

这种方法有什么优点吗？与多退出版本相比？

并不是。

我们还可以使用`?`操作符编写单一退出点方法：

**带 ? 操作符的单一退出点**

```
 public int expression(int x) {
    return  x ==  10 ? -value
        : x > 0  ? value + x
        : 0;
  } 
```

我们从使用语句（if）切换到使用表达式（即返回值的东西）。这使我们能够摆脱额外的变量，同时保持单一退出点。

这个版本比多退出版本更清晰吗？这是值得商榷的，最终是个人口味问题。

使用`?`的代码简洁，但一些人可能会觉得难以理解。

多退出版本更冗长，但其支持者认为更容易理解。

如果你个人偏好`?`操作符版本，这仍然不意味着单一退出点规则是你应该试图普遍应用的东西。

最有可能的结果是，你会促使人们编写类似于我们方法早期臃肿版本的代码。由于 Java 是一种主要基于语句的语言，你也会遇到使用多退出版本时更清晰的逻辑。

马丁·福勒和肯特·贝克在《重构：改善既有代码的设计》中表达得很好

> “. . . 单一退出点真的不是一个有用的规则。清晰是关键原则：如果方法使用单一退出点更清晰，就使用单一退出点；否则不要”

单一退出函数没有问题，但只有在有意义的情况下才编写它们。

# 总是使用 StringBuffer

# 不良建议 - 总是使用 StringBuffer 进行连接

这个建议是错误的。

首先，它主张使用同步的`StringBuffer`而不是`StringBuilder`。

其次，这是对更加微妙和合理的建议不在循环中连接字符串的过度简化或误解。

避免在循环中连接字符串是合理的。如果循环执行了合理次数，使用`StringBuilder`可能更有效，因为它会避免字符串分配。

在大多数情况下，性能差异可能不会显著，但生成的代码并没有明显不易读 - 因此这是一种没有成本的过早优化。

让我们看看当没有循环时应用这个建议会发生什么：

```
 public String buffer(String s, int i) {
    StringBuilder sb = new StringBuilder();
    sb.append("Foo");
    sb.append(s);
    sb.append(i);
    return sb.toString();
  }

  public String concat(String s, int i) {
    return "Foo" + s + i;
  } 
```

`concat`版本更加清晰。

它效率更低吗？

Eclipse 编译器为`concat`生成以下字节码：

```
 NEW java/lang/StringBuilder
    DUP
    LDC "Foo"
    INVOKESPECIAL java/lang/StringBuilder.<init> (Ljava/lang/String;)V
    ALOAD 1
    INVOKEVIRTUAL java/lang/StringBuilder.append /
       (Ljava/lang/String;)Ljava/lang/StringBuilder;
    ILOAD 2
    INVOKEVIRTUAL java/lang/StringBuilder.append (I)Ljava/lang/StringBuilder;
    INVOKEVIRTUAL java/lang/StringBuilder.toString ()Ljava/lang/String;
    ARETURN 
```

编译器在后台创建了一个`StringBuilder`来处理连接，因此我们更简单更清晰的代码生成的字节码与更冗长的选项相同。

代码中的循环存在可能会阻止编译器执行此优化，但没有分支的代码每次都会被优化。尽管可能存在不支持此优化的编译器，但你不太可能会使用它们。

# 匈牙利命名法

# 不良建议 - 匈牙利命名法

匈牙利命名法及类似方案的理念是在变量名称中反映其类型、范围或其他属性。

例如：

+   b 标志

+   n 大小

+   m_nSize

其中`b`表示布尔类型，`n`表示整数类型，`m_`表示命名变量是一个字段。

这是一个糟糕的主意。

如果您正在阅读打印在纸上的代码，这种标记可能有用，但它提供的所有信息在现代 IDE 中都很容易获得。

命名事物本就很困难，而不必再添加额外的要求让名称处理这些问题。

这些类型的标记就像注释一样。它们增加了噪音，并且必须与它们重复的信息一起维护。如果不额外花费精力来维护它们，它们就会误导。

Uncle Bob Martin 表达得很好：

> “如今，匈牙利命名法和其他类型编码形式只是阻碍。它们使得更改变量、函数、成员或类的名称或类型更加困难。它们使得阅读代码更加困难。并且它们可能会误导读者”
