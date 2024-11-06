# 具体内容

# 具体内容

本节提供了有关各种 Java 语言特性和陷阱的一些更具体的建议。

本节所涵盖的内容很大程度上可以由诸如 FindBugs、PMD、Checkstyle 和 Sonar 等工具自动化。

# 知道如何实现 HashCode 和 Equals 方法

## 知道如何实现 HashCode 和 Equals 方法

### 概述

实现 hashCode 和 equals 方法并不简单。除非必须这样做，否则不要实现它们。如果实现了它们，请确保知道自己在做什么。

### 详细信息

众所周知，如果重写 equals 方法，则必须同时重写`hashCode`方法（请参阅《Effective Java》条目 9）。

如果逻辑上相等的对象的`hashCode`不相同，它们在放入`HashMap`等基于哈希的集合中将表现出令人惊讶的行为。

通过“令人惊讶”，我们指的是您的程序将以非常难以调试的方式表现出不正确的行为。

不幸的是，实现 equals 方法实际上很难做到正确。《Effective Java》条目 8 花了大约 12 页来讨论这个主题。

equals 的合同在`java.lang.Object`的 Javadoc 中方便地说明了。我们将不在此重复或重复讨论其含义，这可以在《Effective Java》和互联网的大部分区域找到。相反，我们将看看实现它的策略。

无论采用哪种策略，都很重要，您首先要为您的实现编写测试。

如果代码更改（例如添加字段或更改字段类型），equals 方法很容易导致难以诊断的错误。编写 equals 方法的测试曾经是一项痛苦而耗时的过程，但现在存在着使其变得微不足道的库，可以规定常见情况（请参阅测试 FAQ）。

### 不要

这是最简单的策略，也是您应该默认采用的策略，以保持代码库的精简。

大多数类不需要 equals 方法。除非您的类代表某种值，否则将其与另一个进行比较是毫无意义的，因此请使用从 Object 继承的实现。

一个令人恼火的灰色区域是，生产代码从未要求比较相等性的类，但测试代码却需要。在这种情况下的困境是，是纯粹为了测试的利益而实现方法，还是为了测试代码而复杂化自定义相等性检查。

当然，这里没有正确答案；我们建议首先尝试测试比较方法，然后再提供自定义 equals 方法。

使用诸如 AssertJ 或 Hamcrest 之类的库实现自定义相等性检查可以干净地共享。

《Effective Java》暂时建议，如果意外调用了 equals 方法，则让您的类抛出错误。

```
@Override public boolean equals(Object o) {
  throw new AssertionError(); // Method is never called
} 
```

这似乎是一个好主意，但不幸的是，它将使大多数静态分析工具混淆。总的来说，这可能带来更多问题。

### 使用 IDE 自动生成

大多数 IDE 都提供了一些自动生成 `hashCode` 和 `equals` 方法的方法。这是一种易于访问的方法，但是生成的方法（取决于 IDE 及其设置）通常很丑陋且复杂，例如下面 Eclipse 生成的方法所示：

```
 @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((field1 == null) ? 0 : field1.hashCode());
    result = prime * result + ((field2 == null) ? 0 : field2.hashCode());
    return result;
  } 
```

```
 @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
   MyClass  other = (MyClass) obj;
    if (field1 == null) {
      if (other.field1 != null)
        return false;
    } else if (!field1.equals(other.field1))
      return false;
    if (field2 == null) {
      if (other.field2 != null)
        return false;
    } else if (!field2.equals(other.field2))
      return false;
    return true;
  } 
```

除非您的 IDE 可以配置为生成清理的方法（如下所讨论），我们通常不建议使用此方法。随着时间的推移，手动编辑可能会在此代码中引入错误。

### 手动编写清理方法

Java 7 引入了 `java.util.Objects` 类，使得实现 `hashCode` 变得简单。Guava 提供了类似的 `com.google.common.base.Objects` 类，可以与较早版本的 Java 一起使用。

```
 @Override
  public int hashCode() {
    return Objects.hash(field1, field2);
  } 
```

`Objects` 类还通过将大多数空检查推送到 `Objects.equals` 方法中，稍微简化了实现 equals 的过程。

```
 @Override
  public boolean equals(Object obj) {
    if (this == obj) // <- performance optimisation
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass()) // <- see note on inheritance
      return false;
    MyClass other = (MyClass) obj;
    return Objects.equals(field1, other.field1) &&
        Objects.equals(field2, other.field2);
  } 
```

第一个 `if` 语句在逻辑上并不是必需的，可以安全地省略；但是，它可能会提供性能优势。

通常，我们建议不要包含这种微小的优化，除非已经证明其具有益处。在 equals 方法的情况下，我们建议保留优化。在您的某些类中，这很可能是合理的，并且拥有所有方法遵循相同模板是有价值的。

上面的示例使用 `getClass` 检查对象是否是相同类型。另一种选择是使用 `instanceof`，如下所示

```
 @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (!(obj instanceof MyClass)) // <- compare with instanceof
      return false;
    MyClass other = (MyClass) obj;
    return Objects.equals(field1, other.field1) &&
        Objects.equals(field2, other.field2);
  } 
```

这导致了行为上的不同 - 使用 `instanceof` 比较 `MyClass` 及其子类的实例将返回 true，而使用 `getClass` 将返回 false。

在《Effective Java》中，Josh Bloch 提倡使用 `instanceof`，因为 `getClass` 的实现违反了 Liskov 替换原则的严格解释。

但是，如果使用 `instanceof`，那么如果子类重写 equals，很容易违反 equals 合同的对称性。即：

```
MyClass a = new MyClass();
ExtendsMyClassWithCustomEqual b = new ExtendsMyClassWithCustomEqual();

a.equals(b) // true
b.equals(a) // false, a violation of symmetry 
```

如果您发现自己处于需要考虑子类是否等于其父类的情况下，请重新考虑您的设计。

在类层次结构中考虑维护 equals 合同是痛苦的，您不应该需要为正常的服务器端编码任务而自己或您的团队这样做。

在大多数情况下，如果您认为您的类实现 `hashCode` 和 `equals` 是有意义的，我们强烈建议您将类声明为 final，以便不需要考虑层次结构。

如果您认为有必要将子类视为与其父类等价的情况，请使用 `instanceof`，但确保父类的 equals 方法被声明为 final。

避免比这更复杂的关系。

### Commons EqualsBuilder 和 HashCodeBuilder

Apache commons 的 hashcode 和 equals 构建器曾经是生成这些方法的一种流行方式。我们不建议在新代码中使用它们，因为它们的大部分功能现在已由`java.util.Objects`提供，而不需要引入第三方库，或者通过 Guava 等价物提供。

这些类确实提供了基于单行反射的选项实现。

```
public boolean equals(Object obj) {
  return EqualsBuilder.reflectionEquals(this, obj);
} 
```

```
public int hashCode() {
  return HashCodeBuilder.reflectionHashCode(this);
} 
```

这些实现的简洁性是有吸引力的，但其性能明显较差。良好的性能测试和定期的分析可以帮助确定一个性能较差的方法是否真正导致了应用程序的性能瓶颈。如果您确信您会检测到这些不利影响，那么使用这些方法作为初始占位符实现可能是一个合理的方法。但总的来说，我们建议您避免使用它们。

### 代码生成器

存在许多项目可以在构建时自动生成值对象。其中两个较为知名的选项是：

+   [Google auto](https://github.com/google/auto/tree/master/value)

+   [Project Lombok](https://projectlombok.org/)

但还有许多其他的选择。

#### Google Auto

Google *Auto* 将创建一个带有`@AutoValue`注解的抽象类的*明显*实现的子类。此实现将包括功能性的`hashcode`和`equals`方法。

```
import com.google.auto.value.AutoValue;

@AutoValue
abstract class Animal {
  static Animal create(String name, int numberOfLegs) {
    return new AutoValue_Animal(name, numberOfLegs);
  }

  Animal() {}

  abstract String name();
  abstract int numberOfLegs();
} 
```

这显然比手工制作一个完整的`Animal`类要少努力，但也有一些缺点。

一些与代码生成器相关的问题在 "谨慎考虑代码生成器" 中进行了讨论，将其分类为*摩擦*和*意外*。

在这里，Google Auto 引入了一些*摩擦*，因为上面显示的代码在 IDE 中无法编译，直到生成器运行以产生`AutoValue_Animal`类为止。

还有一些*意外*。

因为它是一个值，Animal 通常会被实现为一个 final 类 - 但我们被迫将其设置为抽象类。 *Auto* 团队建议您添加一个包私有的构造函数以防止其他子类被创建。

与普通的 Java 不同，访问器的声明顺序很重要，因为生成器使用它来定义构造函数参数的顺序。因此，重新排序访问器可能会产生引入错误的令人惊讶的效果。

#### Lombok

Lombok 也可以（除其他事项外）生成值对象的完整实现。

它采用了与 Google auto 不同的方法。

给定一个如下所示的带注解的类：

```
@Value
public class ValueExample {
  String name;
  @NonFinal int age;
  double score;
} 
```

它将在构建时修改类以生成一个类似以下的实现：

```
public final class ValueExample {
  private final String name;
  private int age;
  private final double score;

  public ValueExample(String name, int age, double score) {
    this.name = name;
    this.age = age;
    this.score = score;
   }

  public String getName() {
    return this.name;
  }

  public int getAge() {
    return this.age;
  }

  public double getScore() {
    return this.score;
  }

  public boolean equals(Object o) {
   // valid implementation of equality based on all fields
  }

  public int hashCode() {
   // valid hashcode implementation based on all fields
  } 
```

虽然 Google *Value* 要求程序员为一个类提供一个有效的公共 API，但*Lombok* 根据其内部状态的描述创建了公共 API。该描述是有效的 Java 语法，但在 Lombok 解释时具有不同的含义。

*Lombok*会引起一些摩擦。在没有理解它的 IDE 的情况下，使用*Lombok*是不现实的 - 使用自动生成的 API 的代码将看起来是无效的。必须安装一个 IDE 插件。

一旦安装了 IDE 插件，它（可以说）比 auto 引入的摩擦更小，但*Lombok*的行为更加令人惊讶。解释*Auto*的作用很容易 - 它在构建时生成一个实现您定义的接口的类。预测或解释*Lombok*将做什么要困难得多。

尽管*Lombok*要求程序员编写的代码比*Auto*等解决方案少，但它与普通 Java 的偏离更大。

如果考虑使用代码生成器生成 Value 类，我们建议您在考虑*Lombok*之前考虑*Auto*等方法。

值得称赞的是，*Lombok*提供了一个逃生通道（见“更喜欢可逆决策”），即`delombok`，它允许你输出生成的类。然后可以用这些类替换被注解的原始类。

同样，去除*Auto*也很简单 - 生成的类可以检入源代码树。然后可以通过简单的重构来删除人为的抽象类/实现分离。

# 不要重新分配参数

## 不要重新分配参数

### 总结

方法的参数不应该被重新分配。

### 详情

重新分配参数会使代码难以理解，并且与创建新变量相比没有任何有意义的优势。

如果方法很大，跟踪参数的生命周期可能会很困难。即使在短方法中，重复使用参数也会导致问题。由于变量用于表示两个不同的概念，通常无法有意义地命名它。

如果需要另一个与参数相同类型的变量，应该在本地声明。

**糟糕**

```
public String foo(String currentStatus) {
  if ( someLogic() ) {
    currentStatus  = "FOO";
  }
  return currentStatus;
} 
```

**更好**

```
public String foo(final String currentStatus) {
  String desiredStatus = currentStatus;
  if ( someLogic() ) {
    desiredStatus = "FOO";
  }

  return desiredStatus ;
} 
```

参数可以声明为 final，以便读者一眼就能看出其值不会改变。

# 限制作用域

## 将变量限制在尽可能小的作用域内

### 总结

变量应该尽可能晚声明，以便它们具有尽可能狭窄的作用域。

### 详情

*糟糕*

```
public void foo(String value) {
    String calculatedValue;
    if (someCondition()) {
        calculatedValue = calculateStr(value);
        doSomethingWithValue(calculatedValue);
    }
} 
```

*更好*

```
public void foo(String value) {
    if (someCondition()) {
        String calculatedValue = calculateStr(value);
        doSomethingWithValue(calculatedValue);
    }
} 
```

*更好*

```
public void foo(String value) {
    if (someCondition()) {
        doSomethingWithValue(calculateStr(value));
    }
} 
```

有时，将值赋给命名良好的临时变量会比内联调用方法产生更易读的代码，因为它有助于读者跟踪数据和逻辑流程。

作为一个经验法则，如果你无法为一个变量想出一个名字，而这个变量几乎只是从一个方法中获取值，那么这个变量应该被消除。

# 更喜欢使用`for each`循环而不是`for`循环

## 更喜欢使用`for each`循环而不是`for`循环

### 总结

更喜欢使用`for each`循环而不是索引`for`循环。

### 详情

Java 5 引入的`for each`循环避免了索引 for 循环可能出现的偏差问题，并且比使用迭代器的代码更简洁。

*糟糕*

```
 public List<String> selectValues(List<Integer> someIntegers) {
    List<String> filteredStrings = new ArrayList<String>();
    for (int i = 0; i != someIntegers.size(); i++) {
      Integer value = someIntegers.get(i);
      if (value > 20) {
        filteredStrings.add(value.toString());
      }
    }
    return filteredStrings;
  } 
```

*稍微好一点*

```
 public List<String> selectValues(List<Integer> someIntegers) {
    List<String> filteredStrings = new ArrayList<String>();
    for (Integer value : someIntegers) {
      if (value > 20) {
        filteredStrings.add(value.toString());
      }
    }
    return filteredStrings;
  } 
```

# 更喜欢使用 Maps 和 Filters 而不是命令式循环

## 更喜欢使用 Maps 和 Filters 而不是命令式循环

### 总结

命令式循环将应用程序逻辑隐藏在样板代码中 - 更喜欢映射和过滤器，因为它们将逻辑与实现分离。

### 细节

大多数基于循环的代码可以使用过滤器和映射以更声明式的方式重写。

Java 8 通过引入 lambda 和 streams API 使这变得容易，但是在 Java 7 中也可以使用匿名内部类和第三方库（如 Guava）来应用相同的风格。

过滤器和映射突出了代码的预期目标。这在命令式实现中不太明显。

**糟糕**

```
 public List<String> selectValues(List<Integer> someIntegers) {
    List<String> filteredStrings = new ArrayList<String>();
    for (Integer value : someIntegers) {
      if (value > 20) {
        filteredStrings.add(value.toString());
      }
    }
    return filteredStrings;
  } 
```

**更好（Java 8）**

```
 public List<String> selectValues(List<Integer> someIntegers) {
    return someIntegers.stream()
        .filter(i -> i > 20)
        .map(i -> i.toString())
        .collect(Collectors.toList());
  } 
```

**更好（Java 7 使用 Guava）**

```
 public List<String> selectValues(List<Integer> someIntegers) {
    return FluentIterable
    .from(someIntegers)
    .filter(greaterThan(20))
    .transform(Functions.toStringFunction())
    .toList();
  }

  private static Predicate<Integer> greaterThan(final int limit) {
    return new Predicate<Integer>() {
      @Override
      public boolean apply(Integer input) {
        return input > limit;
      }
    };
  } 
```

请注意，尽管 Java 7 版本需要更多的代码行数（以丑陋的匿名内部类的形式出现），但`selectValues`方法的逻辑更清晰。如果在多个地方需要 Predicate 或 mapping Function 中的逻辑，则可以轻松将其移至公共位置。这在命令式版本中更难实现。

还要注意，创建 Predicate 的方法已经被设为静态的。在返回匿名类时，将其设为静态是一个好主意，以防止长时间的实例阻止父类被垃圾回收。虽然在这个例子中 Predicate 只是短暂存在，但在所有情况下都敷衍地应用静态可以避免思考的开销。

# 避免使用史前的 API

## 避免使用史前的 API

### 总结

不要使用`Vector`，`StringBuffer`和 JDK 的其他过时部分。

### 细节

Java 已经存在了 20 多年。为了保持向后兼容性，它积累了各种各样的 API，这些 API 现在不再合理使用。其中一些方便地标有@Deprecated 注解，其他则没有。

不幸的是，许多人仍然在大学课程和在线示例中使用它们。新的 Java 程序员可能不知道它们已经被替换了 - 一些需要注意的包括：

+   `java.util.Vector` - 使用`ArrayList`代替

+   `java.lang.StringBuffer` - 使用`StringBuilder`代替

+   `java.util.Stack` - 使用`Dequeue`（例如`ArrayDeqeue`）

+   `java.util.Hashtable` - 使用`Map`（例如`HashMap`）

+   `java.util.Enumeration` - 使用`Iterator`或`Iterable`

这些替换（除了`Enumeration`）与原始内容不同，因为它们没有同步。如果你认为你需要一个同步的集合，请找个安静的地方思考一下。

# 注意转换和泛型警告

## 注意转换和泛型警告

### 总结

转换削弱了 Java 类型系统的好处，使代码既不易读也不安全。

尽可能避免转换。

如果你发现自己正在编写一个，请停下来问问自己为什么要写它。

在你的代码中需要做哪些改变，以便你不需要编写该转换？

为什么你不能做出那个改变？

### 细节

Java 的类型系统是为了帮助我们 - 它在编译时捕获错误并记录我们的代码，使其更容易理解和导航。

当我们向代码添加转换时，我们失去了这两个好处。

强制转换会出现在代码中的三个主要原因：

1.  我们已经达到了 Java 类型系统的极限，程序员必须控制

1.  代码的整体设计很差

1.  代码使用原始泛型类型

我们将以相反的顺序查看这些问题。

#### 具有原始类型的代码

如果代码包含原始泛型类型（要么是因为代码早于 Java 5，要么是因为程序员不熟悉 Java），那么将需要进行强制转换。

例如：

```
List list = numberList();
for (Object each : list) {
  Integer i = (Integer) each;
  // do things with integers
} 
```

编译器不会高兴我们未能完全声明我们正在处理的`List`类型，并且将（取决于如何配置）在声明`list`的行上生成错误或警告，例如。

```
List is a raw type. References to generic type List<E> should be parameterized 
```

同样，对于错误的代码，例如：

```
List l = new ArrayList<Number>();
List<String> ls = l; 
```

编译器将发出：

```
The expression of type List needs unchecked conversion to conform to List<String> 
```

确保所有这些警告都得到解决，可以通过实施零编译器警告政策或通过配置编译器��其视为错误来解决。

在这种情况下，移除强制转换和警告都很简单：

```
List<Integer> list = numberList();
for (Integer each : list) {
   // do things with each
} 
```

#### 设计不佳

有时，移除强制转换或修复警告并不是一件简单的事情。我们遇到了第二个问题 - 设计不佳。

例如：

```
List<Widget> widgets = getWidgets();
List results = process(widgets);

for (Object each : results) {
  if (each instanceof String) {
    // handle failure using data from string
  } else {
    EnhancedWidget widget = (EnhancedWidget) each;
    widget.doSomething();
  }
} 
```

通常，放入集合中的对象应该是单一类型或由共同的超类或接口相关的多种类型。

在这里，不相关的类型被放入同一个列表中，使用字符串来传达有关如何“处理”小部件失败的某种信息。

这段代码的经典 OO 修复方法是引入一个具有两个具体实现的`ProcessResult`接口。

```
interface ProcessResult {
 void doSomething();
}

class Success implements ProcessResult {

  private final EnhancedWidget result;

  @Override
  public void doSomething() {
    result.doSomething();
  }

}

class Failure implements ProcessResult {

  private final String result;

  @Override
  public void doSomething() {
    // do something with result string
  }

} 
```

然后可以修复原始代码如下：

```
List<Widget> widgets = getWidgets();
List<ProcessResult> results = process(widgets);

for (ProcessResult each : results) {
    each.doSomething();
  }
} 
```

或者，在 Java 8 中更简洁地表示为：

```
 List<ProcessResult> results = process(widgets);
 results.stream().forEach(ProcessResult::doSomething); 
```

有时使用不相交联合类型，也称为`Either`，也是有道理的。

这种技术在重新处理使用混合类型原始集合的遗留代码时可以特别有用，但在处理错误条件时也是一个明智的方法。

不幸的是，Java 没有提供一个内置的`Either`类型，但在其最简单的形式下看起来是这样的：

```
public class Either<L,R> {
  private final L left;
  private final R right;

  private Either(L left, R right) {
    this.left = left;
    this.right = right;
  }

  public static <L, R> Either<L, R> left(final L left) {
    return new Either<L, R>(left,null);
  }

  public static <L, R> Either<L, R> right(final R right) {
    return new Either<L, R>(null,right);
  }

  boolean isLeft() {
    return left != null;
  }

  L left() {
    return left;
  }

  R right() {
    return right;
  }

} 
```

Atlassian 的 Fugue 等库提供了功能更丰富的实现。

使用 Java 7 中简单形式的`Either`，代码可以重写为：

```
List<Widget> widgets = getWidgets();
List<Either<ProcessResult,String>> results = process(widgets);

for (Either<ProcessResult,String> each : results) {
  if (each.isLeft()) {
    // handle failure using data from string
  } else {
    each.right().doSomething();
  }
} 
```

虽然大多数 Java 程序员更喜欢早期的 OO 版本，但这个版本有两个优点：

1.  这不需要改变原始代码的*结构* - 我们实际上所做的只是让类型记录正在发生的事情

1.  它需要更少的代码

这种模式可以帮助快速驯服难以理解的遗留代码库。

#### 类型系统的限制

有时我们确实会达到 Java 类型系统的极限，需要进行强制转换。

在执行此操作之前，我们必须确保强制转换是安全的，并且没有更好的解决方案。

同样，有时我们可能需要抑制泛型警告，可以通过使用`@SuppressWarnings`进行注释来实现，例如。

```
@SuppressWarnings("unchecked")
<T> T read(final Class<T> type, String xml) {
  return (T) fromXml(xml);
}

Object fromXml(final String xml) {
  return ... // de-serialise from string
} 
```

在这里，编译器无法知道已将什么类型序列化为字符串。希望程序员知道，否则将会发生运行时错误。

# 不要使用魔法数字

## 不要使用魔法数字

### 总结

魔法数字应该替换为描述其含义的良好命名的常量。

#### 详细

将数字或字符串字面量直接放入源代码中会引起两个问题：

1.  文字的**意义**很可能不会清晰。

1.  如果值发生变化，则需要更新所有重复了文字的地方。

因此，文字应该用良好命名的常量和枚举替换。

**不好**

```
public void fnord(int i) {
  if (i == 1) {
    performSideEffect();
  }
} 
```

**更好的**

```
public void fnord(int i) {
  if (i == VALID) {
    performSideEffect();
  }
} 
```

**你误解了重点**

```
public void fnord(int i) {
  if (i == ONE) {
    performSideEffect();
  }
} 
```

如果您提取的常量与可识别的概念相关，请改用枚举：

**好的**

```
public void fnord(FnordStatus status) {
  if (status == FnordStatus.VALID) {
    performSideEffect();
  }
} 
```

一些编码标准会说出诸如“0 和 1 是此规则的例外”的声明。然而，这是一个过于简化了的说法。

有时，0 和 1 会作为低级代码的一部分具有清晰的局部含义，例如：

```
 if (list.size() == 0) {...} 
```

但是，0 和 1 也可能具有特定于域的值，应该像任何其他文字一样提取为常量。

服务器端 Java 通常也可以以更清晰的方式进行重写，而无需使用数字字面量，例如：

```
 if (list.isEmpty()) {...} 
```

# 不要使用 Assert 关键字

## 不要使用 Assert 关键字

### 总结

断言是一种有用的编码技术，可以提供许多好处，但在大多数情况下，最好使用第三方库而不是`assert`关键字来实现它们。

### 详细信息

使用`assert`关键字编写的断言仅在设置了`-ea` JVM 标志时启用。

此标志的意图是允许在开发和测试中启用断言，但在生产中禁用以避免断言逻辑的性能开销。这通常是一种过早的优化，并增加了错误的机会，因为代码在开发和生产中的行为将有所不同。

在生产中关闭断言也会大大削弱它们的价值。如果出现编码错误，断言可确保其尽早报告，接近错误。如果在生产中关闭断言，则错误可能会悄悄传播。这可能会使其后果更严重，并且肯定会使问题更难以诊断。

因此，出于这些原因，除非您正在处理非常注重性能的域，否则应始终启用断言。

总是使用诸如 Guava 的前置条件等第三方库提供的解决方案比`assert`关键字更好。

另一个问题是在测试中使用`assert`关键字。这通常是对 Java 和 JUnit 不熟悉的结果。

在野外找到的代码库中，如果在测试中使用了`assert`，则很少设置`-ea`标志，这意味着测试永远不会失败。对于测试，应始终使用 JUnit 的内置断言或现代面向测试的断言库，例如 AssertJ。

# 避免使用浮点数和双精度数

## 避免使用浮点数和双精度数

### 总结

避免使用浮点数和双精度数（原始数据类型和其包装器）。

### 详细信息

浮点数和双精度数引入了一系列舍入和比较问题。虽然它们对于一些领域是明智的选择，其中你不关心舍入误差，但对于服务器端业务代码来说，整数或`BigDecimal`通常是更好的选择。

核心问题在于浮点数无法表示许多数字（例如`0.1`）。

这会导致意想不到的结果，可能不会被简单的测试用例捕捉到。

```
 double balance = 2.00;
    double transationCost = 0.10;
    int numberTransactions = 6;

    System.out.printf("After %s transactions balance is %s"
                    , numberTransactions
                    , balance - (transationCost * numberTransactions));
    // Gives After 6 transactions balance is 1.4 :-) 
```

但是

```
 double balance = 2.00;
    double transationCost = 0.10;
    int numberTransactions = 7;

    System.out.printf("After %s transactions balance is %s"
                     , numberTransactions
                     , balance - (transationCost * numberTransactions));
    // Gives After 7 transactions balance is 1.2999999999999998 :-( 
```

在这种情况下最简单的解决方案是用整数值替换浮点数（即以分为单位跟踪余额，而不是以美元为单位）。

在无法用整数替换浮点数的情况下，代码可以重写以使用`BigDecimal`。

```
 BigDecimal balance = new BigDecimal("2.00");
    BigDecimal transationCost = new BigDecimal("0.10");

    BigDecimal numberTransactions = BigDecimal.valueOf(7);

    System.out.printf("After %s transactions balance is %s"
                     , numberTransactions
                     , balance.subtract(transationCost.multiply(numberTransactions)));

   // Gives After 7 transactions balance is 1.30 :-) 
```

请注意，尽管`BigDecimal`可以从浮点数构造，但这会让我们回到起点。

```
 BigDecimal balance = new BigDecimal("2.00");
    BigDecimal transationCost = new BigDecimal(0.10); // <- float used to construct

    BigDecimal numberTransactions = BigDecimal.valueOf(7);

    System.out.printf("After %s transactions balance is %s"
                     , numberTransactions
                     , balance.subtract(transationCost.multiply(numberTransactions)));

   // Gives After 7 transactions
   // balance is 1.2999999999999999611421941381195210851728916168212890625 
```

### 何时使用浮点数和双精度数

浮点数和双精度数显然不可能全都是坏的，否则它们不太可能被包含在 Java 语言中。

原始浮点类型在高度数值领域（如机器学习、物理引擎、科学应用等）比`BigDecimal`具有性能优势，这些领域中性能优势可能远远超过额外错误风险。

使用`BigDecimal`的代码也本质上比使用基本类型的代码更冗长和笨拙。如果你在一个可以接受浮点类型不精确的领域工作，你可能更喜欢它们允许的更干净的代码，但请确保你在理解相关风险的情况下有意识地做出这个选择。

# 不要使用反射。

## 不要使用反射。

### 总结

不要在你的代码中使用反射（即`java.lang.reflect`包中的任何内容）。

### 详情

反射是一个强大的工具；它使 Java 能够做一些否则要么是不可能的，要么需要大量样板代码的事情。

但是，虽然在创建框架或库时有时很有用，但它不太可能是解决我们在正常服务器端应用代码中遇到的问题的好方法。

那么，为什么我们要避免使用 Java 提供的强大工具呢？

反射有三个主要缺点：

#### 编译时安全性的丧失

反射将错误从编译时移至运行时 - 这是一件坏事™。

编译器是我们防范缺陷的第一道防线，类型系统是我们用来记录代码的最有效工具之一。我们不应该轻易放弃这些东西。

#### 重构安全性的丧失

重构和代码分析工具对反射是盲目的。

尽管它们可能会尝试考虑到这一点，反射为程序可能的行为方式带来的额外可能性意味着工具不再能提供对程序理解的严格保证。在存在反射的情况下，否则安全的重构可能会改变程序，分析工具可能会报告不正确的结果。

#### 更难理解的代码

就像反射使得自动化工具更难理解代码一样，它也使得人类更难理解代码。

反射会带来意外。

*这个方法从未被调用，我可以安全地删除它。* 哦。反射。

*我可以安全地更改这个私有方法的行为，因为我知道它是从哪里调用的。* 哦。反射。

# 了解 JDK 的一行代码

## 了解常见的一行代码

### 总结

JDK 包含了一些应该用来替换更冗长代码的实用函数。

### 详情

如“优化可读性而非性能”中所讨论的，我们应该更倾向于简单的代码而不是我们认为可能更高效的复杂代码（除非我们通过分析和性能测试证明更复杂的代码确实有真正的好处）。

有时候，我们会发现自己处于一种幸福的情况，我们不需要在代码的清晰度和（假定的）性能之间做出权衡。有时候，也有理由相信代码的最清晰版本可能也稍微更高效。

JDK 中散布着许多小函数，它们比通常用来替代的代码更清晰，可能稍微更高效。应尽可能使用这些函数，一旦您知道它们的存在，任何不使用它们的代码看起来都会有些不对劲。

大多数集成开发环境（IDEs）都会提示您使用这些一行代码中的一部分或全部。

## java.util.Arrays.asList

当您需要将数组转换为固定大小列表时。

List <string class="hljs-class">ss = Arrays.asList(“1”, “2”);</string>

这比通常见到的替代方法更清晰、更高效，比如：

List <string class="hljs-class">ss = new ArrayList<>(); ss.add(“1”); ss.sdd(“2”);</string>

`asList` 返回的列表实现是专门的，可能比 ArrayList 消耗稍微更少的内存。

请注意，此方法创建的列表并非完全不可变。它们是固定大小的，如果尝试添加或删除成员，将抛出 java.lang.UnsupportedOperation，但修改方法如 `set` 将成功。

如果您正在使用 Java 9，`List.of` 方法提供了一个更优越的替代方案。

## java.util.Collections.empty*

`java.util.Collections` 类包含了创建不可修改版本的常见集合类的方法，专门用于包含零个条目或单个条目。

最常见的是：

+   `emptyMap`

+   `emptyList`

+   `emptySet`

+   `singletonList`

+   `singletonMap`

+   `singletonSet`

但也有其他更专业的方法。

再次，与常见的替代方法和返回的专用数据结构相比，使用这些方法会产生更清晰、更描述性的代码，而且可能具有稍微更小的占用空间。

如果您正在使用 Java 9，静态的 `of` 方法提供了一个更优越的替代方案来替代单个条目的方法。

## valueOf

形式：

```
Boolean b = Boolean.valueOf(true); 
```

在主观上更丑陋的情况下，这比稍微更高效：

```
Boolean b = new Boolean(true); 
```

`valueOf`将返回两个固定的布尔实例之一，而调用构造函数将始终分配一个新对象。

类似地，对于整数，`valueOf`将为-128 到 127 之间的值返回一个共享实例。

`Long.valueOf`同样会从缓存中返回对象。

Oracle JDK 目前在调用`valueOf`时不使用缓存来存储浮点数或双精度数。因此，与为浮点数使用`new`相比，使用`valueOf`可能没有优势，但也没有劣势。

`valueOf`方法的重载版本从字符串构造所需的类型。如果您需要从字符串创建装箱的原始类型，这就是方法。

值得注意的是，尽管规范没有保证，但实际上 Java 编译器通过调用`valueOf`来实现自动装箱。

因此：

```
Boolean b = true; 
```

并且

```
Boolean b = Boolean.valueOf(true); 
```

是等价的。

从 Java 9 开始，装箱的原始类型构造函数已被弃用，而是推荐使用`valueOf`和解析方法（见下文）。

## parseXXX

与`valueOf`类似，`parseXXX`方法将字符串转换为原始类型，只是在这种情况下，原始类型没有被装箱。

```
float f = Float.parseFloat(“1.2”); 
```

这正是方法所说的，与常见的替代方法相比：

```
float f = new Float(“1.2”); 
```

它避免了构造和拆箱浮点对象。

类似的方法也适用于布尔值、双精度浮点数、整数和其他原始类型。

## isEmpty

一个常见的笨拙习语是通过检查其大小来检查集合是否为空：

```
if ( list.size() == 0 ) {
  // do stuff
} 
```

更清晰和更简洁：

```
if ( list.isEmpty() ) {
  // do stuff
} 
```

取决于调用它的数据结构，它也可能更具计算效率。

通常没有性能差异，但对于大型`ConcurrentLinkedQueue`，差异可能很大。

## Java 9 工厂方法

Java 9 为 List、Set 和 Map 接口添加了静态工厂`of`方法。

这些允许我们干净地构造集合，例如。

```
List.of(1, 2, 3);
Set.of(42); 
```

`of`方法被重载为最多 10 个值。

该代码比 Java 8 的`Arrays.asList`版本稍微更易读，并返回一个完全结构不可变的列表，不允许替换元素。它也可能稍微更有效率，因为它避免了分配数组。

尽管`of`被重载为不带参数，但这种表达意图不如`emptyList`等清晰，因此可能仍然更受青睐。
