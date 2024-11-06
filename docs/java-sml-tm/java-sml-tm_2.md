# 风格

# 风格

编程风格有许多方面，从放置大括号和换行符的平凡问题到如何设计和构造代码的更有趣的问题。

本节将从更抽象的问题开始，然后深入到更具体的问题。

尽管静态分析工具可以衡量许多讨论中讨论的事物的方面，但在大多数情况下，它们无法就代码是否良好做出破坏性的决定。需要熟练的人来权衡和谨慎应用。

# 仔细考虑代码生成器

# 总结

代码生成器可以自动实现某些类型的功能，节省时间并消除某些类别的错误可能性。

尽管它们有很多值得推荐的地方，但代码生成器也有一个需要在将其纳入项目之前仔细考虑的成本。

偏爱允许生成功能和非生成功能之间明确分离的生成器，但在将任何生成器纳入项目之前，请确保您了解所做的权衡。

## 详情

代码生成器可以分为三种一般类型：

+   样板生成器

+   编译时注解处理器

+   运行时生成器/框架

### 样板生成器

样板生成器是代码生成的最简单形式。它们可以进一步分为：

+   将代码插入现有类中的生成器（例如 IDE 自动生成的方法）。

+   生成产生脚手架的代码，这些代码被检入版本控制并进行修改。

+   从模型生成新类的生成器。生成的代码通常不会被检入版本控制。

我们建议第一种类型的使用要谨慎，如果有的话。这在"了解如何实现 Hashcode 和 Equals"中进一步讨论。

从模型（如模式或语法）生成代码可能是一种有用的方法，只要生成的代码不被修改并且被单独打包。如果生成的代码和非生成的代码打包在同一个模块中，那么这可能开始引起摩擦（见下文）。

### 编译时注解处理器

JSR 269 引入了一个标准框架，用于在构建时处理注解。存在几种工具使用 JSR 269 生成代码。

大多数仅将带注解的类作为输入，从中生成新类。通常，新类扩展或实现带注解的类或接口，但仍保持独立。这实际上只是基于模型的样板生成器的一个子集，其中输入模型是带注解的 Java 类。

一些（如项目 Lombok）会更新带注解的类本身，添加额外的行为。这可能会增加*惊喜*和*摩擦*，下文将讨论这些问题。

### 缺点

显然，代码生成器有很多优点，那么为什么它们不总是合理呢？

它们引起的主要问题是*惊喜*和*摩擦*。

#### 惊喜

如果在编译或运行时生成代码，那么你就不再是在编写 Java 代码了。

你正在编写一个增强版的 Java，它会做一些维护代码的开发者可能不知道的事情。

它可能会做一些他们意想不到的事情。

它可能会打破程序员对于代码中可以发生什么或不能发生什么的基本假设。

运行时生成器通常会比编译时系统生成更多的惊喜 - 它们添加了一个打破通常 Java 规则的*魔法*元素。运行时生成器通常也会削弱类型安全性，将开发者通常期望在编译时发生的问题类别移动到运行时。

当开发者在项目中第一次遇到代码生成器时，它所做的一切都会让人惊讶。

经过一段学习之后，大部分的惊喜应该会消失，但每个开发者都需要经历这个学习期。所涉及的学习可能是显著的 - 比如完全理解 Spring 这样的框架是一个显著的努力。

最令人担忧的问题是在最初的学习期之后仍然存在一些惊喜。

如果在系统出现意外情况时你发现自己问自己“这可能是因为代码生成器吗？”并且每次都必须排除这种可能性，那么你已经为项目引入了一个非常真实的成本。

#### 摩擦

使用编译时生成器的代码在 IDE 中不会干净地导入，除非 IDE 知道如何运行生成器。即使系统受到 IDE 的支持，也可能需要安装插件、设置配置选项等。

摩擦的程度以及遇到的频率将取决于 IDE 和支持的质量。可能会有很少的摩擦，只有在新开发者加入项目时才会遇到。或者可能会很大，并且每次清理代码时都会触发。

减少摩擦的最有效方法是将生成的代码与依赖它的代码分开打包。生成的代码然后成为一个正常的二进制依赖项，而它是自动化的事实则成为一个内部实现细节。

尽管这样做效果很好，但也可能有一个缺点。它可能会创建人为的模块。如果代码不是自动生成的，那么将其打包为单独的模块是否有意义呢？

运行时生成器通常不会引入太多摩擦，尽管有时在从 IDE 运行测试时缺少 javaagents 可能会遇到问题。

### 折衷

所以这些就是问题所在。

与免费功能的承诺相比，惊喜和摩擦听起来像是次要问题，但它们的影响可能是显著的。

是否引入代码生成器是否有意义通常取决于它将被使用的程度。如果有大量功能可以自动生成，那么可能是有意义的，如果数量相对较小，最好还是坚持使用原始的 Java。

# 为可读性进行优化

## 优化可读性而非性能

### 摘要

不要过早优化您的代码。

集中精力使其简单易懂。

### 详情

许多新程序员担心他们编写的每个方法的性能，避免他们认为效率低下的代码，并以试图最小化对象分配、方法调用、赋值或其他他们认为会产生成本的因素的风格编写。

尽管它通常降低可读性并增加复杂性，但大多数微性能优化根本不提供性能优势。

在我们工作的环境中，性能应该是最后考虑的问题之一。相反，应该注意使代码尽可能简单和可读。

如果出现性能问题，应使用性能分析来确定问题实际所在。

这并不意味着性能应完全被忽略，但它应始终被代码的可读性和简单性所取代，直到可以证明优化有真正的好处为止。如果可以以更有效的方式编写代码而不增加任何复杂性或牺牲可读性，则应优先选择（假定）更有效的代码。

# 更喜欢可读性高的代码而不是注释

## 更喜欢可读性高的代码而不是注释

### 摘要

仅使用评论解释代码本身无法解释的内容。

如果您要写评论，请首先考虑是否有办法更改代码，使其无需注释即可理解。

### 详情

来自 Robert C Martin 的《代码整洁之道》。

*“没有什么比一个恰到好处的评论更有帮助。没有什么比轻率的教条性评论更能混淆模块。没有什么比一个传播谎言和错误信息的陈旧评论更有害。”*

评论应仅用于解释无法重构以自我解释的代码背后的意图。

*糟糕*

```
// Check to see if the employee is eligible for full benefits
if ((employee.flags & HOURLY_FLAG) &&
(employee.age > 65)) 
```

*更好*

```
if (employee.isEligibleForFullBenefits()) 
```

只有在解释代码本身无法解释的内容时，注释才有用。

这意味着您写的任何评论都应提供**为什么**，而不是**什么**或**如何**

*糟糕*

```
// make sure the port is greater or equal to 1024
if (port < 1024) {
  throw new InvalidPortError(port);
} 
```

*更好*

```
// port numbers below 1024 (the privileged or “well-known ports”)
// require root access, which we don’t have
if (port < 1024) {
  throw new InvalidPortError(port);
} 
```

*更好*

```
if (requiresRootPrivileges(port)) {
  throw new InvalidPortError(port);
}

private boolean requiresRootPrivileges(int port) {
  // port numbers below 1024 (the privileged or "well-known ports")
  // require root access on unix systems
  return port < 1024;
} 
```

在这里，功能意图已经在方法名中体现出来，注释仅用于提供一些上下文，解释为什么逻辑是合理的。

魔法数字也可以替换为常量。

```
final static const HIGHEST_PRIVILEDGED_PORT = 1023;

private boolean requiresRootPrivileges(int port) {
  // The privileged or "well-known ports" require root access on unix systems
  return port <= HIGHEST_PRIVILEDGED_PORT;
} 
```

然而，评论可能仍然有价值 - 至少它给了不熟悉该主题的读者两个关键短语在网上搜索。

# 谨慎使用 Javadoc

## 谨慎使用 Javadoc

### 摘要

Javadoc 可以帮助文档化代码，但通常有更好的方法来做到这一点。在决定编写之前，请仔细考虑。

### 详情

#### Javadoc 是好的

对于无法访问源代码的外部团队来说，Javadoc 是无价的。

所有外部使用的代码应该为其公共方法编写 Javadoc。

确保所有这样的 Javadoc 都集中在方法做什么，而不是如何做到这一点。

#### Javadoc 是糟糕的

Javadoc 重复了应该从代码本身清晰看出的信息，并带来了持续的维护成本。

如果它不与代码同步更新，那么它就会变得误导。

不要为只有你的团队使用和维护的代码编写 Javadoc。相反，努力确保代码本身清晰表达。

# 记住 Kiss 和 Yagni

## 记住 KISS 和 YAGNI

### 摘要

尽可能保持设计简单。

只创建你现在需要的功能 - 而不是你认为未来可能需要的功能。

### 详情

KISS（保持简单，傻瓜）和 YAGNI（你不会需要它）的首字母缩写提供了值得在编码时记住的好建议。

KISS 建议我们尽可能保持代码和设计简单。

很少有人会不同意这一点，但不幸的是，*简单*并不总是明显的含义。

给定一个问题的两个解决方案，哪个更简单？

+   哪个代码行数最少？

+   哪个类数量最少？

+   哪个使用的第三方依赖更少？

+   哪个分支语句更少？

+   哪个逻辑最明确？

+   哪个与其他地方使用的解决方案一致？

以上所有都是*简单*的合理定义。没有一个是单一的定义总是有意义遵循。

认识到简单并不容易，保持事物简单需要大量工作。

如果我们能够衡量软件的复杂性，我们会发现每个软件片段都必须包含一些最小值。

如果软件再简单一点，那它就会更少功能。

真实的程序总是包含这种*固有复杂性*加上一点。这额外的复杂性是我们添加的*偶然复杂性*，因为我们不完美。

区分偶然复杂性和固有复杂性当然也很困难。

幸运的是，YAGNI 给了我们一些建议，如何保持事物简单，而不必区分偶然和固有复杂性。

系统做的越多，整体复杂性就越高。如果我们制作一个功能更少的系统，它将更简单 - 它将具有更少的*固有复杂性*和更少的*偶然复杂性*。

因此，你的目标是创建解决当前问题的最少功能。

+   不要实现你认为将来可能需要的功能。如果需要，就在未来实现。

+   不要试图使事物“灵活”或“可配置”。让它们只做它们需要做的事情 - 在需要的时候对其进行参数化。

如果你创建的功能超过最小量，你将有更多代码需要调试、理解和维护，直到有人有信心删除它。

# 更倾向于组合

## 更倾向于组合而非继承

### 摘要

组合通常会导致更灵活的设计。

首先考虑使用组合，然后只有在组合似乎不合适时才退而使用继承。

### 细节

组合意味着通过将其他东西添加到一起来构建事物。继承是通过扩展基于现有类的行为来构建事物的。

以一个最小的例子来说- 如果一个类需要接受并存储 String 值的要求，一些新接触 Java 的程序员会选择继承如下：

```
class InheritanceAbuse extends ArrayList<String> {

  public void performBusinessLogic(int i) {
    // do things with stored strings
  }

} 
```

相同的功能可以使用组合来实现。

```
class UsesComposition {

  private final List<String> values = new ArrayList<String>();

  public void performBusinessLogic(int i) {
    // do things with stored strings
  }

  public void add(String value) {
    this.values.add(value);
  }

} 
```

尽管需要更多的代码，但有经验的 Java 程序员甚至不会考虑第一种方法。那么为什么第二个版本更可取呢？

有几种重叠的解释，我们将从最抽象的开始，然后转向更实用的解释。

#### 继承是一个强关系

继承用于建模一个 IS-A 关系 - 即，我们在说我们的`InheritanceAbuse`类是一个 ArrayList，我们应该能够将其传递给接受 ArrayList 的任何代码片段。

组合创建了一个 HAS-A 关系；这是一个较弱的关系，我们应该始终在我们的代码中更倾向于较弱的关系。

因此，更青睐组合而不是继承只是更一般的建议的一个具体实例，即更青睐我们类之间的弱关系。

当存在 IS-A 关系时使用继承是有意义的，但纯粹为了重用代码而使用继承是不适当的机制。

#### 继承破坏了封装

继承实现未封装一个实现细节 - 我们正在一个 ArrayList 中存储东西。

我们类的接口包括从 ArrayList 中提取的各种方法，例如：

+   清除

+   移除

+   包含

这些方法对我们的类有意义吗？如果有人调用它们，是否会干扰`performBusinessLogic`中的逻辑？

我们对我们的示例类的作用了解不够，无法明确回答这些问题，但答案很可能是我们宁愿不暴露这些方法。

如果我们从 ArrayList 切换到其他列表实现，则此更改对类的客户端可见。即使不调用特定于 ArrayList 的方法，以前编译的代码现在可能会中断 - 仅仅更改类型就可能导致编译失败。

#### 我们只能这样做一次

Java 不支持多重继承，所以我们只能选择一个要扩展的东西。如果我们的类还需要存储整数，那么继承甚至都不是一个选项，所以我们必须使用组合。

在单一继承语言中，组合本质上更加灵活。

#### 组合有助于测试

这与我们简单示例无关，但通过组合连接在一起的类如何交互是微不足道的。当使用继承时，测试它们之间的交互要困难得多。

```
class MyUntestableClass extends SomeDependency {
  public void performBusinessLogic(int i) {
    // do things using methods from SomeDependency
  }
} 
```

```
class MyClass {
  private final SomeDependency dependency;

  MyClass(SomeDependency dependency) {
    this.dependency = dependency;
  }

  public void performBusinessLogic(int i) {
    // do things with dependency
  }
} 
```

将模拟对象注入`MyClass`很容易。存在一些技巧来将`MyUntestableClass`中的代码与`SomeDependency`隔离，以进行单元测试，但它们要复杂得多。

#### 继承是静态的

继承在编译时设置了具体类之间的固定关系。使用组合可以在运行时替换不同的具体类。

再次，组合本质上更灵活。

### 接口继承

倾向于使用组合而不是继承的建议是指*实现继承*（即扩展类）。上述讨论的缺点不适用于*接口继承*（即实现接口）。

实际上，您经常需要做的设计选择是实现继承还是组合和接口继承的结合。

在这些情况下，建议仍然倾向于使用组合的方法。

例如，众所周知的基于组合的装饰者模式：

```
class ProcessorUpperCaseDecorator implements Processor {

  private final Processor child;

  ProcessorUpperCaseDecorator(Processor child) {
    this.child = child;
  }

  @Override
  public void process(String someString) {
    child.process(someString.toUpperCase());
  }

} 
```

也可以使用继承实现

```
class InheritanceUpperCaseDecorator extends ConcreteProcessor {

  @Override
  public void process(String someString) {
    super.process(someString.toUpperCase());
  }

} 
```

但是，再次说，这种解决方案会更不灵活。

基于组合的版本，我们可以装饰任何`Processor`。使用继承版本，我们需要为每个我们希望添加大写行为的具体类型重新实现装饰者。

许多常见的 OO 模式依赖于组合和接口继承的结合。

### 何时使用实现继承

几乎任何可以使用实现继承实现的内容也可以使用接口继承和组合的结合实现。

那么何时应该使用实现继承呢？

实现继承在编写时比较简洁。

因此，当**同时**满足以下两个条件时，应该使用实现继承

1.  存在一个需要建模的 IS-A 关系

1.  基于组合的方法将导致过多的样板代码

第二点遗憾地完全是主观的。

# 符合 SOLID 原则

## 符合 SOLID 原则

### 总结

SOLID 首字母缩写提供了一些应该遵循的设计指导。

+   **单一职责原则**

+   **开闭原则**

+   **里氏替换原则**

+   **接口隔离原则**

+   **依赖反转原则**

### 细节

#### 单一职责原则

将您的关注点分开 - 一个类应该只做一件事情。换句话说，一个类应该只有一个改变的理由。

#### 开闭原则

您应该能够扩展行为，而无需修改现有代码。

*"… 您应该设计永远不会更改的模块。当需求变化时，通过添加新代码来扩展此类模块的行为，而不是通过更改已经运作的旧代码。"*

*— 罗伯特·马丁*

表明您可能没有遵循这一原则的迹象是您的代码中存在`switch`语句或`if/else`逻辑。

#### 里氏替换原则

派生类必须能替换其基类。

表明您违反这一原则的一个迹象是您的代码中存在`instanceof`语句。

#### 接口隔离原则

接口隔离原则规定，客户端不应被强制实现他们不使用的接口；更喜欢小而精细的接口而不是大而笼统的接口。

破坏这个原则的一个迹象是在你的代码中存在空方法或抛出 `OperationNotSupportedException` 的方法。

#### 依赖反转原则。

高层模块不应该依赖于低层模块。两者都应该依赖于抽象。

抽象不应该依赖于细节。细节应该依赖于抽象。

在实践中，这意味着你应该遵循以下两种模式之一：

1.  将“高级”组件所依赖的接口与该组件一起打包。

1.  将组件所依赖的接口与客户端和实现分开打包。

这第一种方法是经典的依赖反转（与将高级组件依赖于较低层的传统方法相对比）。

第二种方法被称为“分离的接口模式”。它稍微重量级一些，但更加灵活，因为它不做任何关于谁应该拥有接口的假设。

破坏这个原则的一个迹象是你的代码中存在循环依赖。

# 保持你的代码干燥。

## 保持你的代码干燥。

### 摘要。

不要重复自己（DRY）- 避免多次编写相同的逻辑。

每次复制粘贴代码时，都给自己眼睛一击。这是一个很好的阻止复制粘贴的办法，但随着时间的推移可能会导致失明。

### 细节。

如果同样的逻辑需要多次，则不应该重复；而应该提取到一个命名合适的类或方法中。

这将更易于阅读和维护，因为逻辑需要更改时只需要在一个地方进行更改。

*糟糕的*

```
class Foo {
   private int status;
   private boolean approved;

   foo() {
     if (status == 12 || approved) {
       doFoo();
     }
   }

   bar() {
     if (status == 12 || approved) {
       doBar();
     }
   }
} 
```

*更好的*

```
class Foo {
   private final static int PRE_APPROVED = 12;

   private int status;
   private boolean approved;

   foo() {
     if (isApproved()) {
       doFoo();
     }
   }

   bar() {
     if (isApproved()) {
       doBar();
     }
   }

   private isApproved() {
     return status == PRE_APPROVED || approved;
   }
} 
```

当我们有类似但不相同的逻辑时，事情就会变得有些棘手。

虽然这很快很容易，但我们能做的最糟糕的事情就是复制粘贴。

**可怕的**

```
public void doSomething(List<Widget> widgets) {
  for (Widget widget : widgets) {
    reportExistence(widget);
    if (widget.snortles() > 0) {
      reportDeviance(widget);
      performSideEffect(widget);
    }
  }
}

public void doSomethingSimilar(List<Widget> widgets) {
  for (Widget widget : widgets) {
    reportExistence(widget);
    if (widget.snortles() > 0) {
      reportDeviance(widget);
      performDifferentSideEffect(widget);
    }
  }
} 
```

现在看起来很快很容易，但这是一个每次我们试图理解或改变它时都会消耗时间的代码库的开始。

一个简单但非常有限的重用代码的方法是引入布尔标志。

**不是太好**

```
public void doSomething(List<Widget> widgets) {
  doThings(widgets, false);
}

public void doSomethingSimilar(List<Widget> widgets) {
  doThings(widgets, true);
}

private void doThings(List<Widget> widgets, boolean doDifferentSideEffect) {
  for (Widget widget : widgets) {
    reportExistence(widget);
    if (widget.snortles() > 0) {
      reportDeviance(widget);
      if (doDifferentSideEffect) {
        performDifferentSideEffect(widget);
      } else {
        performSideEffect(widget);
      }
    }
  }
} 
```

这很丑陋，在可能性增加时会变得更糟。

更可扩展的方法是使用策略模式。

如果我们引入一个接口：

```
interface WidgetAction {
   void apply(Widget widget);
} 
```

然后我们可以这样使用它：

**更好的**

```
public void doSomething(List<Widget> widgets) {
  doThings(widgets, performSideEffect());
}

public void doSomethingSimilar(List<Widget> widgets) {
  doThings(widgets, performDifferentSideEffect());
}

private WidgetAction performSideEffect() {
  return new WidgetAction() {
    @Override
    public void apply(Widget widget) {
      performSideEffect(widget);
    }
  };
}

private WidgetAction performDifferentSideEffect() {
  return new WidgetAction() {
    @Override
    public void apply(Widget widget) {
      performDifferentSideEffect(widget);
    }
  };
}

private void doThings(List<Widget> widgets, WidgetAction action ) {
  for (Widget widget : widgets) {
    reportExistence(widget);
    if (widget.snortles() > 0) {
      reportDeviance(widget);
      action.apply(widget);
    }
  }
} 
```

由于匿名内部类样板代码，Java 7 版本相当冗长。

可以说，对于非常简单的情况，布尔标志可能更可取，但是，如果我们将 `performSideEffect` 和 `performDifferentSideEffect` 方法中的逻辑提取到实现 `WidgetAction` 的顶级类中，那么策略版本就变得令人信服。

在 Java 8 中，即使在最简单的情况下，策略模式也是更可取的。

**使用 Java 8 更好**

```
public void doSomething(List<Widget> widgets) {
  doThings(widgets, widget -> performSideEffect(widget));
}

public void doSomethingSimilar(List<Widget> widgets) {
  doThings(widgets, widget -> performDifferentSideEffect(widget));
}

private void doThings(List<Widget> widgets, Consumer<Widget> action ) {
  for (Widget widget : widgets) {
    reportExistence(widget);
    if (widget.snortles() > 0) {
      reportDeviance(widget);
      action.accept(widget);
    }
  }
} 
```

我们不需要引入自己的接口 - 内置的`Consumer<T>`就足够了。如果`doThings`方法被公开暴露，或者`performSideEffect`中的逻辑足够复杂以至于需要提取到顶层类中，我们应该考虑引入一个接口。

循环也可以转换为管道。

**作为管道**

```
private void doThings(List<Widget> widgets, Consumer<Widget> action ) {
  widgets
  .stream()
  .peek(widget -> reportExistence(widget))
  .filter(widget -> widget.snortles() > 0)
  .peek(widget -> reportDeviance(widget))
  .forEach(action);
} 
```

# 更喜欢可逆的决策

## 更喜欢可逆的决策

### 摘要

更喜欢易于更改的设计决策。

### 详情

在设计代码时做出的许多决策最终会被证明是错误的。

如果您可以通过包含其后果和添加抽象使决策可逆，那么这种未来的变化就不重要。

例如 - 如果您引入第三方库并在整个代码中引用它，那么撤销使用该库的决定的成本就会很高。如果将其限制在一个位置并为其创建一个接口，则撤销决定的成本就很低。

但不要忘记 KISS 和 YAGNI - 如果您的抽象使设计复杂化，那么最好将其排除。

# 明确表明依赖关系

## 明确和可见地表明依赖关系

### 摘要

确保类的依赖关系是清晰可见的。

始终使用构造函数将依赖项注入类中。不要使用其他方法，如 setter 或字段上的注解。

永远不要使用隐藏路径（如`Singletons`或`ThreadLocals`）引入依赖关系。

### 详情

如果每个对象依赖的接口和类都是显眼可见的，代码就更容易理解。

最显眼的依赖关系是作为参数注入方法中的依赖关系。

存储为字段的依赖关系不太显眼，但是根据这些字段如何填充，依赖关系仍然相对容易发现。

#### 构造函数注入

构造函数依赖注入清晰地传达了对象的依赖关系，并确保对象只能在有效状态下创建。它允许字段被设为**final**，以便它们的生命周期是明确的。

这是注入依赖关系的唯一方式。

#### Setter 注入

Setter 注入增加了对象可能处于的状态数量。其中许多状态将是无效的。

如果使用 setter 注入，类可能以半初始化状态构造。什么构成完全初始化状态只能通过检查代码来确定。

**糟糕**

```
public class Foo() {
  private Bar bar;

  public void doStuff() {
    bar.doBarThings();
  }

  public void setBar(Bar bar) {
    this.bar = bar;
  }
} 
```

在这里，如果构造`Foo`时没有调用`setBar`，将抛出`NullPointerException`。

**更好**

```
public class Foo() {
  private final Bar bar;

  public Foo(Bar bar) {
    this.bar = bar;
  }

  public void doStuff() {
    bar.doBarThings();
  }
} 
```

在这里，很明显我们必须提供一个`Bar`，因为没有它我们无法构造这个类。

#### 字段注解

虽然字段上的注解看起来很方便，但这意味着依赖关系在公共 API 中不可见。它们还将类的构造与理解它们的框架联系起来，并阻止字段被设为 final。

不应该使用字段注解。

如果您正在使用诸如 Spring 等依赖注入框架，请将对象的构建移动到配置类中或将注解的使用限制在构造函数上。这两种方法都允许正常构造您的类，并确保所有依赖关系可见。

#### 隐藏的依赖

任何不是使用构造函数或方法参数注入到类中的东西都是隐藏的依赖。

这些都是邪恶的。

它们是从`Singletons`，`ThreadLocals`，静态方法调用或者简单地调用`new`引入的。

**不好**

```
public class HiddenDependencies {
  public void doThings() {
    Connection connection = Database.getInstance().getConnection();
    // do things with connection
    ....
  }
} 
```

在这里，我们必须确保在调用下面代码的 `doThings` 方法之前 `Database` 类处于有效状态，但是我们没有办法知道这一点，除非查看每一行代码。

**更好**

```
public class HiddenDependencies {
  private final Database database;

  public HiddenDependencies(Database database) {
    this.database = database;
  }

  public void doThings() {
    Connection connection = database.getConnection();
    // do things with connection
    ....
  }
} 
```

通过构造函数注入使依赖性清晰可见。

根据定义，隐藏的依赖是难以发现的，但它们还有第二个问题 - 它们也难以替换。

#### Seams

Seams 是由 Michael Feathers 在 "Working Effectively with legacy code" 中介绍的一个概念。

他定义它为：

> "一个可以在程序中修改行为而不在该地方编辑的地方。"

在 `HiddenDependencies` 的原始版本中，如果我们想要用一个模拟或存根来替换 `Database`，我们只能在单例提供一些方法来修改它返回的实例的情况下这样做。

**不是一个好方法**

```
public class Database implements IDatabase {
  private static IDatabase instance = new Database();

  public static IDatabase getInstance() {
    return instance;
  }

  public static void setInstanceForTesting(IDatabase database) {
    instance = database;
  }

} 
```

这种方法引入了一个接缝，但并未解决我们对可见性的担忧。依赖性仍然隐藏。

如果我们采用这种方法，我们的代码库将仍然难以理解，我们将不断地与测试顺序依赖进行斗争。

使用构造函数注入，我们获得了一个接缝并使依赖性可见。即使 `Database` 是一个单例，我们仍然可以将我们的代码与之隔离以进行测试。

# 更喜欢不可变对象

## 更喜欢不可变对象

### 概要

在可能的情况下，创建不能被更改的对象 - 特别是如果这些对象将是长期存在或全局可访问的。

### 细节

可变状态使程序变得更难理解和维护。

当对象的生命周期短暂且不离开方法范围时，可变状态几乎不会造成问题。写入和读取将会紧密地相邻，并且会有一个清晰的顺序。

对于较长寿命的对象，情况更加复杂。

如果一个对象从一个方法中逃逸出来，那么它可能会在代码中的多个位置被访问到。

我们必须首先假设这些对象可能发生的任何事情都会发生。我们只能通过检查整个程序来确认某些情况不会发生。

与可变对象相比，不可变对象可能发生的事情的范围要小得多。通过限制长期存在的对象的行为方式，我们使事情变得更简单。我们需要考虑的可能性更少。

不幸的是，从类定义中并不总是容易看出该类型对象的生命周期将是什么样的。也许只会创建短寿实例。也许只会创建长寿实例。也许两者都有。

如果我们默认设计不可变类，我们就不需要担心这个问题。

#### 可变对象的问题

如果我们有一个非常简单的类，比如`Foo`

```
public class Foo {
  private Long id;

  public Long getId() {
    return id;
  }

  public void setId(Long id) {
    this.id = id;
  }

  @Override
  public int hashCode() {
    return Objects.hashCode(id);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    Foo other = (Foo) obj;
    return Objects.equals(id, other.id);
  }
} 
```

我们需要搜索我们的代码库以确定以下内容：

##### 从多个线程中永远不会访问

`Foo`不是线程安全的。

对 long 的写入不是原子的，`Foo`本身没有建立字段写入和读取之间的 happens-before 关系。

如果`setId`和`getId`从不同线程调用，我们可能会得到过时或垃圾值。

##### 在`Foo`被放入集合后从未调用`setId`

这个类的`hashcode`依赖于一个可变字段。如果我们在将其放入集合后修改它，那么我们的程序将不会按照我们的期望行为。

##### 我们数据的流动

即使我们的程序表现正确，我们仍需要做一些工作来理解它的功能。

`setId`可以在对象创建后的任何时候调用。因此，我们只能通过查找所有对`setId`的调用来理解数据在程序中的流动方式 - 可能有几个，也可能只有一个。我们能发现这一点的唯一方法是检查整个程序。

#### 不可变对象

如果我们可以使我们的对象不可变，我们将获得保证，无需担心对象的使用方式。

```
@Immutable
public final class Foo {
  private final Long id;

  public Foo(Long id) {
    this.id = id;
  }

  public Long getId() {
    return id;
  }

  @Override
  public int hashCode() {
    return Objects.hashCode(id);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    Foo other = (Foo) obj;
    return Objects.equals(id, other.id);
  }
} 
```

`Foo`是长寿还是短寿已经不再重要。

它本质上是线程安全的。

我们知道我们构造的任何值都将保持不变直到它死去。只有一个可能的数据写入点，因此我们不需要搜索其他地方��

##### 注解

该示例使用 JSR3051 `javax.annotation.concurrent.Immutable`注解。

这并不以任何方式改变对象的功能，但提供了一种传达这个类是不可变的意图的方式。静态分析工具，比如[Mutablility Detector](https://github.com/MutabilityDetector/MutabilityDetector)，可以检查这个意图是否被违反。

一眼就能看出`Foo`是不可变的，因为它有一个已知的不可变类型的 final 字段。

`final`关键字只确保字段指向的引用不会改变。

如果字段是`Bar`类型，那么我们不知道它是否可变，除非检查`Bar`以查看它是否也是不可变的。即使我们不使用静态分析工具，使用`Immutable`注解也会加快这一评估过程。

而不是更新不可变对象的状态，我们创建保留我们不希望修改的状态的新实例。

这种模式对一些 Java 程序员来说起初似乎很奇怪，但编程模型类似于熟悉的`String`类的工作方式。

```
@Immutable
public final class Bar {
  private int anInt;
  private String aString;

  public Bar(int anInt, String aString) {
    this.anInt = anInt;
    this.aString = aString;
  }

  @CheckReturnValue
  public Bar withAnInt(int anInt) {
    return new Bar(anInt, this.aString);
  }

  @CheckReturnValue
  public Bar withAString(String aString) {
    return new Bar(this.antInt, aString);
  }
} 
```

可通过调用`withAString`和`withAnInt`获得具有新值的`Bar`实例。

JSR305 `javax.annotation.CheckReturnValue` 允许静态分析工具（如 [Error Prone](https://github.com/google/error-prone)）在发现错误（例如下面的代码中）时发出警告。

```
public Bar doThings(Bar bar) {
  if(someLogic()) {
    bar.withAnInt(42);
  }
  return bar;
} 
```

这里调用 `withAnInt` 不会产生任何效果，因为返回值没有存储。最有可能的是，程序员打算写：

```
public Bar doThings(Bar bar) {
  if(someLogic()) {
    return bar.withAnInt(42);
  }
  return bar;
} 
```

#### 何时使用可变对象

可变对象比不可变对象稍微少些样板代码。

如果你知道一个类只会用于创建短暂的局部对象，那么你可能会考虑使其可变。但是你必须权衡这一点，因为随着代码库的增长，需要确保该类只用于这种方式会增加额外的工作量。

存在选项可以自动生成不可变和可变类，从而消除了可变对象的主要优势。这些选项中的两个在“了解如何实现 Hashcode 和 Equals”中进一步讨论。

可变对象曾经是 Java 中的常态。因此，许多常见的框架需要可变对象。持久化和序列化框架通常需要没有参数构造函数和设置器的 Java beans。其他框架可能要求您使用两阶段构造，其中包括初始化等生命周期方法。

虽然文档中并不总是突出显示，但一些长期存在的框架已经更新以支持不可变对象。

例如，Jackson 现在允许构造函数和工厂方法进行注释：

```
public class Foo {
  private final int x
  private final int y;

  @JsonCreator
  public Foo(@JsonProperty("x") int x, @JsonProperty("y") int y) {
   this.x = x;
   this.y = y;
  }
} 
```

其他框架，如 Hibernate，只能与提供默认构造函数的类一起使用。虽然它们可以配置为直接设置字段而无需使用设置器，但这样做会引起更多问题。

如果你受限于一个需要可变性的框架，那么你将需要在与该框架进行接口时使用可变对象。

# 使用一致的代码布局

## 在每个项目中使用一致的代码布局

### 总结

在每个代码库中达成一致并强制执行标准的代码格式方案。

### 细节

Java 代码的格式和布局主要是个人喜好的问题。

有些风格（例如在条件语句中省略大括号）可以认为会使某些类型的错误稍微更有可能。

其他风格可能需要更多的工作来保持代码的一致性（例如将字段对齐成列），但是总的来说，没有哪种特定方案比其他方案优越得多。

尽管如此，程序员对此事往往有着强烈的意见。

每个代码库都应该有一个统一的约定格式样式，该样式应该得到一致应用，并且被所有在该代码库上工作的人所理解。

这可以防止提交战争，其中不同团队成员会根据个人喜好重新格式化代码。这也使得代码更易于理解，因为如果格式在文件之间发生根本性变化，则读者会有认知成本。

尽管一致性很重要，但也有成本。

如果团队之间已经就应该如何格式化内容达成广泛一致，试图强制执行一套官方规则很可能会带来更多的不满而非好处。

因此应该设置一个全局首选参考，但是团队应该自由地偏离这个参考，只要它们维护的代码使用一致的风格即可。

### 建议的格式化规则

如果你没有自己的强烈偏好，我们建议你遵循[Google Java Style](https://google.github.io/styleguide/javaguide.html)。

这些格式化规则经过深思熟虑，文档清晰，不过于规范。

我们在这里不会详细描述它们，但是按照这些规则格式化的代码将看起来类似于以下内容：

```
class Example {
  int[] myArray = {1, 2, 3, 4, 5, 6};
  int theInt = 1;
  String someString = "Hello";
  double aDouble = 3.0;

  void foo(int a, int b, int c, int d, int e, int f) {
    if (f == 5) {
      System.out.println("fnord");
    } else {
      System.out.println(someString);
    }

    switch (a) {
      case 0:
        Other.doFoo();
        break;
      default:
        Other.doBaz();
    }
  }

  void bar(List<Integer> v) {
    for (int i = 0; i < 10; i++) {
      v.add(new Integer(i));
    }
  }
} 
```

然而，我们建议忽略谷歌指南中关于何时编写 Javadoc 的指导，而采用我们自己的指导。

#### 关于这种风格的显著特点

##### 使用空格而不是制表符

制表符的外观可能因编辑器的配置方式而有所不同。这将导致不同的程序员根据他们的编辑器设置不断重新格式化文件。使用空格可以避免这个问题。

在某些语言中（例如，在代码最小化器出现之前的 JavaScript 中），制表符具有/曾经具有优势，因为它们可以减小源文件的大小，而不是使用多个空格。对于 Java 来说，源文件的增加大小不相关。

##### 唯一的大括号风格

关于这种风格的所谓优势有各种争论，但我们主要建议使用它是因为它在 Java 社区中很常见。

虽然简单的`if else`语句可以通过省略大括号更简洁地编写，但我们建议始终包含它们。这样可以减少在意图不是这样时语句被放置在条件之外的机会。

# 为易于理解而分组的方法

## 为易于理解而分组的方法

### 总结

类的公共方法应该出现在文件的顶部，私有方法应该出现在底部，而任何受保护或包默认方法应该在它们之间。

除了按照可访问性排列外，它们还应该按照逻辑顺序排列。

### 细节

此方案试图实现两个目标：

1.  通过将公共 API 与实现细节分离来突出显示公共 API

1.  允许读者以最小的滚动量来跟随逻辑流

为了实现第二个目标，方法应该被分成逻辑组，其中方法始终出现在它们调用的方法之上。

这两个目标显然存在冲突，因为将公共 API 方法分组放置在文件顶部会阻止将它们与它们使用的实现方法分组在一起。如果这导致了一个大问题，那么这可能表明类承担了太多的责任，并且可以将其重构为一个或多个较小的类。

当一个实现方法从多个位置调用或方法具有递归关系时，也会出现方法的“正确”位置的问题。 当然，没有一个正确的答案，任何大致符合第二个目标的排序都可以使用。

构造函数和静态工厂方法通常应该放在类的第一位。 方法是静态的这一事实通常不会影响它应该放置的位置。

**例子**

```
public class Layout {

  private int a;

  Layout() {...}

  public static Layout create() {...}

  public void api1() {
    if (...) {
      doFoo();
    }
  }

  public void api2() {
    if(...) {
      doBar();
    }
  }

  private void doFoo() {
    while(...) {
      handleA();
      handleB();
    }
    leaf();
  }

  private void handleA() {...}

  private void handleB() {...}

  private static void doBar() {
    if (...) {
      leaf();
    }
  }

  private void leaf() {...}
} 
```

字段应始终放在任何方法之前的类顶部。

# 保持方法小而简单

## 保持方法小而简单

### 摘要

保持方法小而简单。

### 详情

小东西比大东西更容易理解。 方法也不例外。

通过包含的代码行数来衡量方法的大小是一种方法。

作为指南，方法的长度通常不应超过 7 行。这不是一个硬性规则 - 只是在何时感到不舒服的方法大小的指南。

通过方法的可能路径数量来衡量方法的大小是另一种方法。 方法的*Cyclomatic complexity*可用来衡量这一点 - 随着条件逻辑和循环数量的增加，它将增加。

作为指南，方法的复杂性通常不应超过 5。再次强调，这不是一个硬性规则，只是在何时感到不舒服的指南。

您的代码自然会包含一些比其他方法更大的方法 - 有些概念本质上比其他概念更复杂，如果进一步拆分或以不同的方式表达，实现将不会变得更简单。

但大多数大型方法可以通过以下三种方式之一变得更小：

+   重构为多个较小的方法

+   重新表达逻辑

+   使用适当的语言特性

#### 将方法拆分为较小的关注点

许多大型方法在其中有试图找到出路的较小方法。

通过释放它们可以使我们的代码更易于维护。

**糟糕的**

```
protected static Map<String, String> getHttpHeaders(HttpServletRequest request) {
  Map<String, String> httpHeaders = new HashMap<String, String>();

  if (request == null || request.getHeaderNames() == null) {
    return httpHeaders;
  }

  Enumeration names = request.getHeaderNames();

  while (names.hasMoreElements()) {
    String name = (String)names.nextElement();
    String value = request.getHeader(name);
    httpHeaders.put(name.toLowerCase(), value);
  }

  return httpHeaders;
} 
```

**更好的**

```
protected static Map<String, String> getHttpHeaders(HttpServletRequest request) {
  if ( isInValidHeader(request) ) {
    return Collections.emptyMap();
  }
  return extractHeaders(request);
}

private static boolean isInValidHeader(HttpServletRequest request) {
  return (request == null || request.getHeaderNames() == null);
}

private static Map<String, String> extractHeaders(HttpServletRequest request) {
  Map<String, String> httpHeaders = new HashMap<String, String>();
  for ( String name : Collections.list(request.getHeaderNames()) ) {
    httpHeaders.put(name.toLowerCase(), request.getHeader(name));
  }
  return httpHeaders;
} 
```

#### 重新表达逻辑

**可怕的**

```
public boolean isFnardy(String item) {
  if (item.equals("AAA")) {
    return true;
  } else if (item.equals("ABA")) {
    return true;
  } else if (item.equals("CC")) {
    return true;
  } else if (item.equals("FWR")) {
    return true;
  } else {
    return false;
  }
} 
```

这可以很容易地重新表达，减少噪音：

**更好的**

```
public boolean isFnardy(String item) {
  return item.equals("AAA")
      || item.equals("ABA")
      || item.equals("CC")
      || item.equals("FWR");
} 
```

或采用更声明式的风格：

```
private final static Set<String> FNARDY_STRINGS
  = ImmutableSet.of("AAA",
                    "ABA",
                    "CC",
                    "FWR");

public boolean isFnardy(String item) {
  return FNARDY_STRINGS.contains(item);
} 
```

以上两种变化都不会改变程序的结构，甚至不会影响方法的签名。 它们都减少了行数和复杂性，同时增加了可读性。

通过一系列更高影响力的变化来简化事情，提取我们领域的模型通常是最好的方法。

很难猜测我们构造的示例可能会是什么样子，但很可能可以用多态性替换这个条件逻辑。

```
enum ADomainConcept {
  AAA(true),
  ABA(true),
  CC(true),
  FWR(true),
  OTHER(false),
  ANDANOTHER(false);

  private final boolean isFnardy;
  private ADomainConcept(boolean isFnardy) {
    this.isFnardy = isFnardy;
  }

  boolean  isFnardy() {
    return isFnardy;
  }
} 
```

#### 使用适当的语言特性

方法有时会因解决常见编程问题的模板代码而变得臃肿。 一些模板代码的需求已被新的语言特性所移除。

其中一些*新*特性并不是那么新，但仍然有人在编写没有这些特性的代码：

+   Java 5 泛型消除了丑陋的转换需求

+   Java 5 的 for-each 循环可以替代使用迭代器和索引循环的代码

+   Java 7 的 try-with-resources 可以替代复杂的 try、catch、finally 块

+   Java 7 的多捕获可以替代重复的捕获块

+   Java 8 lambda 表达式可以替代匿名类样板代码

# 方法应该只做一件事

## 方法应该只做一件事

### 摘要

方法应该只做一件事。

#### 详情

《代码整洁之道》中的一条有用指南是，一个函数是否只做一件事。

“另一种了解函数是否做了超过“一件事”的方法是，如果您可以从中提取另一个函数，并且该函数的名称不仅仅是其实现的重新陈述。”

*糟糕*

```
 public void updateFooStatusAndRepository(Foo foo) {
     if ( foo.hasFjord() ) {
        this.repository(foo.getIdentifier(), this.collaborator.calculate(foo));
     }

     if (importantBusinessLogic()) {
       foo.setStatus(FNAGLED);
       this.collaborator.collectFnagledState(foo);
     }
  } 
```

*更好*

```
 public void registerFoo(Foo foo) {
     handleFjords(foo);
     updateFnagledState(foo);
  }

  private void handleFjords(Foo foo) {
      if ( foo.hasFjord() ) {
        this.repository(foo.getIdentifier(), this.collaborator.calculate(foo));
     }
  }

  private void updateFnagledState(Foo foo) {
    if (importantBusinessLogic()) {
       foo.setStatus(FNAGLED);
       this.collaborator.collectFnagledState(foo);
     }
  } 
```

*你走得太远了*

```
 public void registerFoo(Foo foo) {
     handleFjords(foo);
     updateFnagledState(foo);
  }

  private void handleFjords(Foo foo) {
      if ( foo.hasFjord() ) {
        this.repository(foo.getIdentifier(), this.collaborator.calculate(foo));
     }
  }

  private void updateFnagledState(Foo foo) {
    if (importantBusinessLogic()) {
       updateFooStatus(foo);
       this.collaborator.collectFnagledState(foo);
     }
  }

  private void updateFooStatus(Foo foo) {
    foo.setStatus(FNAGLED);
  } 
```

# 避免空值

## 尽量避免使用空值

### 摘要

空值是一个价值连城的错误，请确保知道如何在代码中避免使用它。

尽量减少您或您的客户需要编写以下内容的次数：

```
 if ( != null ) {
    ...
  } 
```

### 详情

尽管您与之交互的库和框架可能返回空值，但您应该尽量确保这种做法仅限于第三方代码。

您的应用程序核心应该假设不必担心空值。

避免空值的策略包括：

+   空对象模式 - 当您认为某些内容是可选的时

+   类型安全的空模式（又称 Option、Optional 和 Maybe）- 当您需要表达接口可能不返回内容时

+   契约式设计

### 空对象模式

空对象模式是避免空值的经典面向对象方法。每当您认为有一个您认为是可选的依赖关系时，应该使用它。

模式非常简单，只需提供一个“什么也不做”或具有中立行为的接口实现。然后客户端可以安全地引用它，无需检查空值。

### 类型安全的空值（又称 Optional）

类型安全的空模式在大多数函数式编程语言中都很常见，它们分别被称为 Maybe、Option 或 Optional。Java 8 最终添加了 Optional 类型，但通过 Guava 和其他库，早期版本也提供了实现。

这是一个简单的模式。Optional 基本上只是一个可以容纳一个或零个值的盒子。您可以通过 `isPresent` 检查盒子是否为空，并通过 get 方法检索其值。

Optional 应该在公共方法可能在正常程序流程中不返回值时使用。

如果您在空的 Optional 上调用 get，它将抛出 `NoSuchElementException`。

可能不会立即明显 Optional 相对于仅使用空值提供了什么价值。如果您需要在调用 `get` 之前检查 Optional 中是否有内容，那么这与检查值不为空以避免 `NullPointerException` 有何不同？

有几个重要的区别。

首先，如果你的方法声明返回 `Optional<Person>`，那么你可以立即从类型签名中看出它可能不会返回一个值。如果它只返回 `Person`，那么只有在查看源代码、测试或文档时才会知道它可能返回空值。

同样重要的是，如果你知道在代码库中总是返回 `Optional`，当某些东西可能不存在时，那么你一眼就知道返回 `Person` 的方法将始终返回一个值，永远不会返回空值。

最后，使用 Optionals 的首选方式不是调用 get 方法或显式检查是否包含值。相反，Optional 中包含的值（或未包含的值）可以通过该类上的各种方法安全地映射、消费和过滤。

在最简单的情况下，可以通过调用 `orElse` 方法来访问可能为空的 Optional，该方法接受一个默认值，如果 Optional 为空，则使用该默认值。

如前所述，使用 Optionals 的最佳时机是方法的返回类型。它们通常不应作为字段保存（在这里使用空对象模式）或传递给公共方法（而是提供不需要该参数的重载版本）。

有时 Java 程序员第一次遇到 Optional 时提出的一个异议是，Optional 本身可能为空。虽然这是真的，但从方法返回空的 Optional 是一种反常的做法，应该被视为编码错误。

存在可以检查返回空值 Optional 的静态分析规则。

### 契约式设计

我们希望我们控制的所有代码都能够忽略空值的存在（除非它与某些强制我们考虑空值的第三方代码进行交互）。

`Objects.requireNonNull` 可以用于添加一个运行时断言，确保空值未传递给方法。

因为你的核心代码通常应假设空值永远不会传递，所以用测试文档化这种行为的价值很小；断言很有价值，因为它们确保错误发生在错误产生的地方附近。

我们也可以在构建时检查这个契约。

JSR-305 提供了可以用来声明接受空值的注释。

尽管 JSR-305 处于休眠状态，并且在不久的将来没有被纳入 Java 中的迹象，但这些注释可以在 maven 坐标处获得：-

```
<dependency>
    <groupId>com.google.code.findbugs</groupId>
    <artifactId>jsr305</artifactId>
    <version>3.0.1</version>
</dependency> 
```

它们受到几种静态分析工具的支持，包括：-

+   [Findbugs](http://findbugs.sourceforge.net/)

+   [Error Prone](http://errorprone.info/)

这些规则可以配置为在不期望传递空值的参数时中断构建。

对每个类、方法或参数进行 `@Nonnull` 注释会很快变得乏味，而且是否值得产生这么多噪音是值得商榷的。

幸运的是，可以通过在 package-info.java 文件中注释一个包来将 `@Nonnull` 设置为默认值，如下所示

```
@javax.annotation.ParametersAreNonnullByDefault
package com.example.somepackage ; 
```

不幸的是，子包不继承其父级的注释，因此必须为每个包创建一个 package-info.java 文件。

一旦非空参数成为默认行为，任何接受 null 的参数都可以用 `@Nullable` 进行注释。

# 大量使用 final。

## 大量使用 final。

### 摘要

考虑使任何不会更改的变量或参数 final。

### 细节

使参数和只赋值一次的变量为 final 会使方法更易于理解，因为它限制了代码中可能发生的事情。

使所有参数和只赋值一次的变量 final 是合理的，但需要权衡在每处插入 `final` 关键字所带来的噪音。

对于短方法来说，利弊是否超过成本是值得争议的，但如果一个方法又大又笨重，那么使事情变得 final 的理由就更加充分。

每个团队都应该就使变量 final 达成一致的政策。

至少，大型方法中的所有内容都应该被设为 final。这也可以根据团队的意愿扩展到较短的方法。一项全面的政策具有易于自动化/理解的优势。更微妙的政策更难以沟通。

在处理遗留代码时，使参数和变量 final 也是在重构之前了解方法的有用第一步。在单次赋值变量为 final 后，表现为难以表达为较小块的方法也将变得更容易理解。

# 提供不超过一个工作构造函数。

## 提供不超过一个工作构造函数。

### 摘要

虽然一个类可能提供许多构造函数，但只有一个应该写入字段并初始化类。

### 细节

在构造期间只有一个地方对字段进行赋值，这样可以很容易地了解该类可以在哪些状态下构造。

类不应该提供设置字段的多个构造函数。

**不好的做法**

```
public class Foo {
  private final String a;
  private final Integer b;
  private final Float c;

  public Foo(String value) {
    this.a = Objects.requireNonNull(value);
    this.b = 42;
    this.c = 1.0f;
  }

  public Foo(Integer value) {
    this.a = "";
    this.b = Objects.requireNonNull(value);
    this.c = 1.0f;
  }

  public Foo(Float value) {
    this.a = "";
    this.b = 42;
    this.c = Objects.requireNonNull(value);
  }
} 
```

上述代码中值的重复可以移除，但仍会令人困惑，因为初始化类的关注点分散在三个位置。

如果添加了更多的字段，很容易忘记在现有构造函数中初始化它们。

幸运的是，我们已经使所有字段都是 final，所以这会导致编译错误。如果类是可变的，我们将在运行时发现一个 bug。

**更好的做法**

```
public class Foo {
  private final String a;
  private final Integer b;
  private final Float c;

  private Foo(String a, Integer b, Float c) {
    this.a = Objects.requireNonNull(a);
    this.b = Objects.requireNonNull(b);
    this.c = Objects.requireNonNull(c);
  }

  public Foo(String value) {
    this(value, 42, 1.0f);
  }

  public Foo(Integer value) {
    this("", value, 1.0f);
  }

  public Foo(Float value) {
    this("", 42, value);
  }
} 
```

现在字段只在一个地方编写，减少了重复。

我们还可以一眼看出 `Foo` 不能用 null 值构造。在之前的版本中，只能通过扫描三个不同的位置来确定。

遵循这个模式，即使是非 final 的字段也很难忘记设置。

# 避免使用已检查异常。

## 避免使用已检查异常。

### 摘要

不要声明已检查异常，除非有明确的应该在抛出异常时采取的行动。

### 细节

异常是用于异常情况的 - 设计你的代码，使其不会在预期发生的情况下抛出异常。

这意味着它们不应该用于正常的控制流程。

受检异常会使代码膨胀和复杂化。除非调用者总是可以采取明确的操作来从错误情况中恢复，否则应避免将它们添加到你的 API 中。

这种情况非常罕见。

如果你正在使用一个使用了受检异常的库，你可以通过重新抛出运行时异常来包装它们。

当你这样做时，请确保保留堆栈跟踪。

```
try {
  myObject.methodThrowingException();
} catch (SomeCheckedException e) {
  throw new RuntimeException(e);
} 
```

如果你捕获了一个`Exception`或`Throwable`，但不确定确切的类型，你可以使用 Guava 的`Throwables.propagate`来避免创建不必要的包装器。

```
try {
  myObject.methodThrowingException();
} catch (Exception e) {
  throw Throwables.propagate(e);
} 
```

这将包装受检异常并按原样重新抛出未检查的异常。
