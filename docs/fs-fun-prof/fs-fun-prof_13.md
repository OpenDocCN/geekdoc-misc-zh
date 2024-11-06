# “F#中的面向对象编程”系列

正如之前多次强调的那样，F#在本质上是一种功能性语言，但面向对象的特性已经很好地集成在其中，没有“外挂”感觉。因此，将 F#仅作为面向对象语言使用，例如作为 C#的替代方案，是完全可行的。

在这个系列中，我们将看看 F#如何支持面向对象的类和方法。

+   F#中的面向对象编程：介绍。

+   类。

+   继承和抽象类。

+   接口。

+   对象表达式。

# F#中的面向对象编程：介绍

# F#中的面向对象编程：介绍

在这个系列中，我们将看看 F#如何支持面向对象的类和方法。

## 是否应该使用面向对象特性？

正如之前多次强调的那样，F#在本质上是一种功能性语言，但面向对象的特性已经很好地集成在其中，没有“外挂”感觉。因此，将 F#仅作为面向对象语言使用，例如作为 C#的替代方案，是完全可行的。

无论是使用面向对象风格还是函数式风格，当然取决于你。以下是一些赞成和反对的观点。

使用面向对象特性的原因：

+   如果你只想直接从 C#进行移植而不进行重构。（更多关于此的信息，请参阅如何从 C#移植到 F#的整个系列。）

+   如果你想将 F#主要用作面向对象语言，作为 C#的替代方案。

+   如果你需要与其他.NET 语言集成

不使用面向对象特性的原因：

+   如果你是一个从命令式语言转变而来的初学者，类可能会成为阻碍你理解函数式编程的绊脚石。

+   类没有“开箱即用”的便利功能，如“纯”F#数据类型具有的内置相等性和比较、漂亮的打印等功能。

+   类和方法与类型推断系统和高阶函数不太兼容（参见这里的讨论），因此大量使用它们意味着你将难以从 F#最强大的部分中受益。

在大多数情况下，最佳方法是混合使用，主要使用纯粹的 F#类型和函数以便从类型推断中受益，但在需要多态性时偶尔使用接口和类。

## 理解 F#的面向对象特性

如果你决定使用 F#的面向对象特性，接下来的一系列文章应该涵盖你在使用 F#中类和方法时需要了解的一切。

首先，如何创建类！

# 类

# 类

这篇文章和接下来的文章将介绍在 F#中创建和使用类和方法的基础知识。

## 定义一个类

就像 F#中的所有其他数据类型一样，类定义以`type`关键字开头。

与其他类型的区别在于，类在创建时总是有一些参数传递进去 -- 构造函数 -- 因此类名后面*总是有括号*。

此外，与其他类型不同，类*必须*附加函数作为成员。本文将解释如何为类执行此操作，但对于将函数附加到其他类型的一般讨论，请参阅类型扩展的文章。

因此，例如，如果我们想要一个名为`CustomerName`的类，该类需要三个参数来构造它，它将被写成这样：

```
type CustomerName(firstName, middleInitial, lastName) = 
    member this.FirstName = firstName
    member this.MiddleInitial = middleInitial
    member this.LastName = lastName 
```

让我们将其与 C# 等效项进行比较：

```
public class CustomerName
{
    public CustomerName(string firstName, 
       string middleInitial, string lastName) {
        this.FirstName = firstName;
        this.MiddleInitial = middleInitial;
        this.LastName = lastName;
    }

    public string FirstName { get; private set; }
    public string MiddleInitial { get; private set; }
    public string LastName { get; private set; }
} 
```

你可以看到在 F# 版本中，主要构造函数嵌入到了类声明本身中 --- 它不是一个单独的方法。也就是说，类声明具有与构造函数相同的参数，并且参数自动成为不可变的私有字段，用于存储传入的原始值。

因此，在上面的示例中，由于我们将`CustomerName`类声明为：

```
type CustomerName(firstName, middleInitial, lastName) 
```

因此`firstName`，`middleInitial`和`lastName`自动成为了不可变的私有字段。

### 在构造函数中指定类型

你可能没有注意到，但上面定义的`CustomerName`类不约束参数为字符串，与 C# 版本不同。通常，从使用中推断的类型推断可能会强制值为字符串，但如果你确实需要明确指定类型，可以像往常一样使用冒号后跟类型名称。

这是一个带有构造函数中显式类型的类的版本：

```
type CustomerName2(firstName:string, 
                   middleInitial:string, lastName:string) = 
    member this.FirstName = firstName
    member this.MiddleInitial = middleInitial
    member this.LastName = lastName 
```

关于 F# 的一个小特性是，如果你需要将元组作为参数传递给构造函数，你将不得不显式地注释它，因为对构造函数的调用看起来是相同的：

```
type NonTupledConstructor(x:int,y: int) = 
    do printfn "x=%i y=%i" x y    

type TupledConstructor(tuple:int * int) = 
    let x,y = tuple
    do printfn "x=%i y=%i" x y    

// calls look identical
let myNTC = new NonTupledConstructor(1,2)    
let myTC = new TupledConstructor(1,2) 
```

### 类成员

上面的示例类具有三个只读实例属性。在 F# 中，属性和方法都使用`member`关键字。

此外，在上面的示例中，你可以看到每个成员名称前面都有一个"`this`"。这是一个"自我标识符"，用于引用类的当前实例。每个非静态成员都必须有一个自我标识符，即使它没有被使用（如上面的属性）。没有使用特定的单词的要求，只要是一致的即可。你可以使用"this"、"self"、"me"或任何其他通常表示自我引用的单词。

## 理解类签名

当类被编译（或当你在编辑器中悬停在定义上时），你会看到类的"类签名"。例如，对于类定义：

```
type MyClass(intParam:int, strParam:string) = 
    member this.Two = 2
    member this.Square x = x * x 
```

对应的签名是：

```
type MyClass =
  class
    new : intParam:int * strParam:string -> MyClass
    member Square : x:int -> int
    member Two : int
  end 
```

类签名包含了类中所有构造函数、方法和属性的签名。了解这些签名的含义很重要，因为就像函数一样，你可以通过它们来理解类的功能。这也很重要，因为当创建抽象方法和接口时，你需要编写这些签名。

### 方法签名

诸如 `how-types-work-with-functions.html` 的独立函数的签名一样，方法签名非常相似，只是参数名称是签名本身的一部分。

因此，在这种情况下，方法签名是：

```
member Square : x:int -> int 
```

作为比较，相应的独立函数的签名是：

```
val Square : int -> int 
```

### 构造函数签名

构造函数签名总是被称为 `new`，但除此之外，它们看起来像一个方法签名。

构造函数签名总是以元组值作为它们唯一的参数。在这种情况下，元组类型是 `int * string`，正如你所期望的那样。返回类型是类本身，同样是你所期望的。

再次，我们可以将构造函数签名与类似的独立函数进行比较：

```
// class constructor signature
new : intParam:int * strParam:string -> MyClass

// standalone function signature
val new : int * string -> MyClass 
```

### 属性签名

最后，诸如 `member Two : int` 的属性签名与独立简单值的签名非常相似，只是没有给出显式的值。

```
// member property
member Two : int

// standalone value
val Two : int = 2 
```

## 使用 "let" 绑定的私有字段和函数

在类声明之后，你可以选择性地有一组“let”绑定，通常用于定义私有字段和函数。

这里有一些演示这一点的示例代码：

```
type PrivateValueExample(seed) = 

    // private immutable value
    let privateValue = seed + 1

    // private mutable value
    let mutable mutableValue = 42

    // private function definition
    let privateAddToSeed input = 
        seed + input

    // public wrapper for private function
    member this.AddToSeed x = 
        privateAddToSeed x

    // public wrapper for mutable value
    member this.SetMutableValue x = 
        mutableValue <- x 

// test
let instance = new PrivateValueExample(42)
printf "%i" (instance.AddToSeed 2)
instance.SetMutableValue 43 
```

在上面的示例中，有三个 `let` 绑定：

+   `privateValue` 被设置为初始种子加 1

+   `mutableValue` 被设置为 42

+   `privateAddToSeed` 函数使用了初始种子加上一个参数

因为它们是 `let` 绑定，所以它们自动是私有的，因此要从外部访问它们，必须有一个公共成员作为包装器。

注意构造函数中传递的 `seed` 值也可以作为私有字段使用，就像 `let` 绑定的值一样。

### 可变的构造函数参数

有时，你希望传递给构造函数的参数是可变的。你不能在参数本身指定这一点，所以标准技术是创建一个可变的 `let` 绑定值，并从参数中赋值，如下所示：

```
type MutableConstructorParameter(seed) = 
    let mutable mutableSeed = seed 

    // public wrapper for mutable value
    member this.SetSeed x = 
        mutableSeed <- x 
```

在这种情况下，给可变值赋予与参数本身相同的名称是非常常见的，像这样：

```
type MutableConstructorParameter2(seed) = 
    let mutable seed = seed // shadow the parameter

    // public wrapper for mutable value
    member this.SetSeed x = 
        seed <- x 
```

## 使用“do”块的附加构造函数行为

在之前的`CustomerName`示例中，构造函数只允许一些值被传入，但不做其他任何事情。然而，在某些情况下，你可能需要执行一些代码作为构造函数的一部分。这是使用 `do` 块来完成的。

这里是一个示例：

```
type DoExample(seed) = 
    let privateValue = seed + 1

    //extra code to be done at construction time
    do printfn "the privateValue is now %i" privateValue 

// test
new DoExample(42) 
```

“do” 代码也可以调用在它之前定义的任何 `let` 绑定的函数，就像在这个例子中所示：

```
type DoPrivateFunctionExample(seed) =   
    let privateValue = seed + 1

    // some code to be done at construction time
    do printfn "hello world"

    // must come BEFORE the do block that calls it
    let printPrivateValue() = 
        do printfn "the privateValue is now %i" privateValue 

    // more code to be done at construction time
    do printPrivateValue()

// test
new DoPrivateFunctionExample(42) 
```

### 在 do 块中通过 "this" 访问实例

“do”绑定和“let”绑定之间的一个区别是，“do”绑定可以访问实例，而“let”绑定则不能。这是因为“let”绑定实际上在构造函数之前就已经被评估了（类似于 C#中的字段初始化器），所以在某种意义上，实例还不存在。

如果需要从“do”块中调用实例的成员，您需要一种方法来引用实例本身。这再次是使用“self 标识符”完成的，但这次它附加到类声明本身。

```
type DoPublicFunctionExample(seed) as this =   
    // Note the "this" keyword in the declaration

    let privateValue = seed + 1

    // extra code to be done at construction time
    do this.PrintPrivateValue()

    // member
    member this.PrintPrivateValue() = 
        do printfn "the privateValue is now %i" privateValue 

// test
new DoPublicFunctionExample(42) 
```

一般情况下，最好不要从构造函数中调用成员，除非必须（例如调用虚方法）。最好调用私有 let-bound 函数，并且如果必要，让公共成员调用同样的私有函数。

## 方法

方法定义非常类似于函数定义，只是它有`member`关键字和 self 标识符，而不只是`let`关键字。

这里有一些例子：

```
type MethodExample() = 

    // standalone method
    member this.AddOne x = 
        x + 1

    // calls another method
    member this.AddTwo x = 
        this.AddOne x |> this.AddOne

    // parameterless method
    member this.Pi() = 
        3.14159

// test
let me = new MethodExample()
printfn "%i" <| me.AddOne 42
printfn "%i" <| me.AddTwo 42
printfn "%f" <| me.Pi() 
```

您可以看到，就像普通函数一样，方法可以具有参数，调用其他方法，并且可以没有参数（或者更准确地说，带有 unit 参数）

### 元组形式与柯里化形式

与普通函数不同，具有多个参数的方法可以通过两种不同的方式进行定义：

+   柯里化形式，其中参数用空格分隔，并支持部分应用。（为什么称为“柯里化”？请参阅柯里化的解释。）

+   元组形式，其中所有参数同时传入，用逗号分隔，放在单个元组中。

柯里化方法更加功能性，元组方法更加面向对象。下面是一个分别采用两种方法的示例类：

```
type TupleAndCurriedMethodExample() = 

    // curried form
    member this.CurriedAdd x y = 
        x + y

    // tuple form
    member this.TupleAdd(x,y) = 
        x + y

// test
let tc = new TupleAndCurriedMethodExample()
printfn "%i" <| tc.CurriedAdd 1 2
printfn "%i" <| tc.TupleAdd(1,2)

// use partial application
let addOne = tc.CurriedAdd 1  
printfn "%i" <| addOne 99 
```

那么你应该使用哪种方法呢？

元组形式的优点是：

+   与其他.NET 代码兼容

+   支持命名参数和可选参数

+   支持方法重载（具有相同名称但函数签名不同的多个方法）

另一方面，元组形式的缺点是：

+   不支持部分应用

+   与高阶函数不太适用

+   不太适用于类型推断

有关元组形式与柯里化形式的更详细讨论，请参阅 type extensions 中的文章。

### 与类方法结合使用的 Let-bound 函数

一个常见的模式是创建执行所有繁重工作的 let-bound 函数，然后让公共方法直接调用这些内部函数。这样做的好处是，与方法相比，类型推断在函数式代码中效果更好。

这里有一个例子：

```
type LetBoundFunctions() = 

    let listReduce reducer list = 
        list |> List.reduce reducer 

    let reduceWithSum sum elem = 
        sum + elem

    let sum list = 
        list |> listReduce reduceWithSum 

    // finally a public wrapper 
    member this.Sum  = sum

// test
let lbf = new LetBoundFunctions()
printfn "Sum is %i" <| lbf.Sum [1..10] 
```

有关如何执行此操作的更多详细信息，请参阅此讨论。

### 递归方法

与普通 let-bound 函数不同，递归方法不需要特殊的`rec`关键字。下面是作为方法的沉闷的熟悉的斐波那契函数：

```
type MethodExample() = 

    // recursive method without "rec" keyword
    member this.Fib x = 
        match x with
        | 0 | 1 -> 1
        | _ -> this.Fib (x-1) + this.Fib (x-2)

// test
let me = new MethodExample()
printfn "%i" <| me.Fib 10 
```

### 方法的类型注解

通常情况下，方法参数和返回值的类型通常可以由编译器推断出来，但如果您需要指定它们，您可以像为标准函数指定方式一样进行指定：

```
type MethodExample() = 
    // explicit type annotation
    member this.AddThree (x:int) :int = 
        x + 3 
```

## 属性

属性可以分为三组：

+   不可变属性，其中有一个“获取”但没有“设置”。

+   可变属性，其中有一个“获取”和一个（可能是私有的）“设置”。

+   只写属性，其中有一个“设置”但没有“获取”。这些很少见，我不会在这里讨论它们，但是如果您有需要，MSDN 文档描述了它们的语法。

不可变和可变属性的语法略有不同。

对于不可变属性，语法很简单。有一个“获取”成员，类似于标准的“let”值绑定。绑定右侧的表达式可以是任何标准表达式，通常是构造函数参数、私有 let 绑定字段和私有函数的组合。

这是一个示例：

```
type PropertyExample(seed) = 
    // immutable property 
    // using a constructor parameter
    member this.Seed = seed 
```

然而，对于可变属性，语法更加复杂。您需要提供两个函数，一个用于获取，一个用于设置。这是通过以下语法实现的：

```
with get() = ...
and set(value) = ... 
```

以下是一个示例：

```
type PropertyExample(seed) = 
    // private mutable value
    let mutable myProp = seed

    // mutable property
    // changing a private mutable value
    member this.MyProp 
        with get() = myProp 
        and set(value) =  myProp <- value 
```

要使设置函数私有化，请改用关键字`private set`。

### 自动属性

从 VS2012 开始，F#支持自动属性，这消除了为它们创建单独的备份存储的要求。

要创建一个不可变的自动属性，请使用以下语法：

```
member val MyProp = initialValue 
```

要创建一个可变的自动属性，请使用以下语法：

```
member val MyProp = initialValue with get,set 
```

请注意，在这个语法中有一个新关键字`val`，并且自身标识符已经消失。

### 完整的属性示例

以下是演示所有属性类型的完整示例：

```
type PropertyExample(seed) = 
    // private mutable value
    let mutable myProp = seed

    // private function
    let square x = x * x

    // immutable property 
    // using a constructor parameter
    member this.Seed = seed

    // immutable property 
    // using a private function
    member this.SeedSquared = square seed

    // mutable property
    // changing a private mutable value
    member this.MyProp 
        with get() = myProp 
        and set(value) =  myProp <- value

    // mutable property with private set
    member this.MyProp2 
        with get() = myProp 
        and private set(value) =  myProp <- value

    // automatic immutable property (in VS2012)
    member val ReadOnlyAuto = 1

    // automatic mutable property (in VS2012)
    member val ReadWriteAuto = 1 with get,set

// test 
let pe = new PropertyExample(42)
printfn "%i" <| pe.Seed
printfn "%i" <| pe.SeedSquared
printfn "%i" <| pe.MyProp
printfn "%i" <| pe.MyProp2

// try calling set
pe.MyProp <- 43    // Ok
printfn "%i" <| pe.MyProp

// try calling private set
pe.MyProp2 <- 43   // Error 
```

### 属性与无参数方法

此时，您可能会对属性和无参数方法之间的区别感到困惑。乍一看，它们看起来相同，但是有一个微妙的区别--“无参数”方法实际上并不是无参数的；它们总是具有一个单位参数。

这里有一个在定义和使用上的区别的示例：

```
type ParameterlessMethodExample() = 
    member this.MyProp = 1    // No parens!
    member this.MyFunc() = 1  // Note the ()

// in use
let x = new ParameterlessMethodExample()
printfn "%i" <| x.MyProp      // No parens!
printfn "%i" <| x.MyFunc()    // Note the () 
```

您还可以通过查看类定义的签名来区分它们

类的定义如下所示：

```
type ParameterlessMethodExample =
  class
    new : unit -> ParameterlessMethodExample
    member MyFunc : unit -> int
    member MyProp : int
  end 
```

该方法的签名为`MyFunc : unit -> int`，属性的签名为`MyProp : int`。

这与如果函数和属性是独立声明的，在任何类外部的情况下，签名会非常相似：

```
let MyFunc2() = 1 
let MyProp2 = 1 
```

这些的签名将如下所示：

```
val MyFunc2 : unit -> int
val MyProp2 : int = 1 
```

这几乎完全相同。

如果您不清楚两者之间的区别以及为什么函数需要单位参数，请阅读无参数方法的讨论。

## 次要构造函数

除了嵌入其声明中的主构造函数外，类还可以具有其他构造函数。这些由`new`关键字指示，并且必须将主构造函数作为它们的最后一个表达式调用。

```
type MultipleConstructors(param1, param2) =
    do printfn "Param1=%i Param12=%i" param1 param2

    // secondary constructor
    new(param1) = 
        MultipleConstructors(param1,-1) 

    // secondary constructor
    new() = 
        printfn "Constructing..."
        MultipleConstructors(13,17) 

// test
let mc1 = new MultipleConstructors(1,2)
let mc2 = new MultipleConstructors(42)
let mc3 = new MultipleConstructors() 
```

## 静态成员

就像在 C# 中一样，类可以具有静态成员，这是用`static`关键字表示的。`static`修饰符在成员关键字之前。

静态成员不能具有自我标识符（例如“this”），因为它们没有实例可以引用。

```
type StaticExample() = 
    member this.InstanceValue = 1
    static member StaticValue = 2  // no "this"

// test
let instance = new StaticExample()
printf "%i" instance.InstanceValue
printf "%i" StaticExample.StaticValue 
```

## 静态构造函数

在 F# 中没有静态构造函数的直接等价物，但您可以创建静态 let 绑定值和静态 do 块，在类首次使用时执行。

```
type StaticConstructor() =

    // static field
    static let rand = new System.Random()

    // static do
    static do printfn "Class initialization!"

    // instance member accessing static field
    member this.GetRand() = rand.Next() 
```

## 成员的可访问性

您可以使用标准 .NET 关键字`public`、`private`和`internal`来控制成员的可访问性。可访问性修饰符在成员关键字之后，在成员名称之前。

与 C# 不同，所有类成员默认为公共，而不是私有。这包括属性和方法。但是，非成员（例如`let`声明）是私有的，不能被公开。

以下是一个示例：

```
type AccessibilityExample() = 
    member this.PublicValue = 1
    member private this.PrivateValue = 2
    member internal this.InternalValue = 3
// test
let a = new AccessibilityExample();
printf "%i" a.PublicValue
printf "%i" a.PrivateValue  // not accessible 
```

对于属性，如果设置和获取具有不同的可访问性，您可以使用单独的可访问性修饰符标记每个部分。

```
type AccessibilityExample2() = 
    let mutable privateValue = 42
    member this.PrivateSetProperty
        with get() = 
            privateValue 
        and private set(value) = 
            privateValue <- value

// test
let a2 = new AccessibilityExample2();
printf "%i" a2.PrivateSetProperty  // ok to read
a2.PrivateSetProperty <- 43        // not ok to write 
```

在实践中，C# 中常见的“公共获取，私有设置”组合在 F# 中通常不需要，因为可以更优雅地定义不可变属性，如前所述。

## 提示：为其他 .NET 代码定义类

如果要定义需要与其他 .NET 代码进行互操作的类，请不要将它们定义在模块内！请将它们定义在命名空间中，而不是在任何模块之外。

这样做的原因是，F# 模块被公开为静态类，模块内定义的任何 F# 类都被定义为静态类内的嵌套类，这可能会影响您的互操作性。例如，一些单元测试运行器不喜欢静态类。

在模块外定义的 F# 类将生成为普通的顶级 .NET 类，这可能是您想要的。但请记住（如在先前的帖子中讨论的），如果您没有明确声明命名空间，您的类将被放置在自动生成的模块中，并且将在您不知情的情况下进行嵌套。

这里有两个 F# 类的示例，一个在模块外定义，一个在模块内定义：

```
// Note: this code will not work in an .FSX script, 
// only in an .FS source file.
namespace MyNamespace

type TopLevelClass() = 
    let nothing = 0

module MyModule = 

    type NestedClass() = 
        let nothing = 0 
```

下面是相同代码在 C# 中的样子：

```
namespace MyNamespace
{
  public class TopLevelClass
  {
  // code
  }

  public static class MyModule
  {
    public class NestedClass
    {
    // code
    }
  }
} 
```

## 构造和使用类

现在我们已经定义了类，如何使用它呢？

创建类的一种方式是直接并且与 C# 类似 -- 使用`new`关键字并传递参数给构造函数。

```
type MyClass(intParam:int, strParam:string) = 
    member this.Two = 2
    member this.Square x = x * x

let myInstance = new MyClass(1,"hello") 
```

然而，在 F# 中，构造函数被视为另一个函数，因此通常可以消除`new`，并单独调用构造函数函数，就像这样：

```
let myInstance2 = MyClass(1,"hello")
let point = System.Drawing.Point(1,2)   // works with .NET classes too! 
```

在创建实现`IDisposible`的类时，如果不使用`new`，编译器会发出警告。

```
let sr1 = System.IO.StringReader("")      // Warning
let sr2 = new System.IO.StringReader("")  // OK 
```

对于可处置的内容，使用`use`关键字而不是`let`关键字可能是有用的。有关更多信息，请参阅关于`use`的帖子。

### 调用方法和属性

一旦你有了一个实例，你可以"点进"该实例，并以标准方式使用任何方法和属性。

```
myInstance.Two
myInstance.Square 2 
```

在上面的讨论中，我们已经看到了许多成员使用的示例，关于这点没有太多要说的。

请记住，如上所述，元组式方法和柯里化式方法可以以不同的方式调用：

```
type TupleAndCurriedMethodExample() = 
    member this.TupleAdd(x,y) = x + y
    member this.CurriedAdd x y = x + y

let tc = TupleAndCurriedMethodExample()
tc.TupleAdd(1,2)      // called with parens
tc.CurriedAdd 1 2     // called without parens
2 |> tc.CurriedAdd 1  // partial application 
```

# 继承和抽象类

# 继承和抽象类

这是对前一篇关于类的文章的延续。本文将重点讨论 F#中的继承，以及如何定义和使用抽象类和接口。

## 继承

要声明一个类继承自另一个类，使用以下语法：

```
type DerivedClass(param1, param2) =
   inherit BaseClass(param1) 
```

`inherit`关键字表示`DerivedClass`继承自`BaseClass`。此外，必须同时调用某个`BaseClass`的构造函数。

此时比较 F#和 C#可能会有用。这里是一个非常简单的一对类的 C#代码。

```
public class MyBaseClass
{
    public MyBaseClass(int param1) {
        this.Param1 = param1;
    }
    public int Param1 { get; private set; }
}

public class MyDerivedClass: MyBaseClass
{
    public MyDerivedClass(int param1,int param2): base(param1) {
        this.Param2 = param2;
    }
    public int Param2 { get; private set; }
} 
```

注意，继承声明`class MyDerivedClass: MyBaseClass`与调用`base(param1)`的构造函数是不同的。

现在这是 F#版本：

```
type BaseClass(param1) =
   member this.Param1 = param1

type DerivedClass(param1, param2) =
   inherit BaseClass(param1)
   member this.Param2 = param2

// test
let derived = new DerivedClass(1,2)
printfn "param1=%O" derived.Param1
printfn "param2=%O" derived.Param2 
```

与 C#不同，声明中的继承部分，`inherit BaseClass(param1)`，包含了要继承的类*和*它的构造函数。

## 抽象和虚拟方法

显然，继承的一部分是能够拥有抽象方法、虚拟方法等。

### 在基类中定义抽象方法

在 C#中，抽象方法由`abstract`关键字加上方法签名来表示。在 F#中，这是相同的概念，只是 F#中函数签名的书写方式与 C#有很大不同。

```
// concrete function definition
let Add x y = x + y

// function signature
// val Add : int -> int -> int 
```

因此，要定义一个抽象方法，我们使用签名语法，加上`abstract member`关键字：

```
type BaseClass() =
   abstract member Add: int -> int -> int 
```

注意等号已被冒号替换。这是你所期望的，因为等号用于绑定值，而冒号用于类型注解。

现在，如果你尝试编译上面的代码，你会得到一个错误！编译器会抱怨该方法没有实现。要解决这个问题，你需要：

+   提供方法的默认实现，或者

+   告诉编译器整个类也是抽象的。

我们很快会看到这两种替代方案。

### 定义抽象属性

抽象的不可变属性的定义方式类似。签名就像简单值的签名一样。

```
type BaseClass() =
   abstract member Pi : float 
```

如果抽象属性是可读/可写的，你需要添加`get/set`关键字。

```
type BaseClass() =
   abstract Area : float with get,set 
```

### 默认实现（但没有虚拟方法）

要在基类中为抽象方法提供默认实现，使用`default`关键字而不是`member`关键字：

```
// with default implementations
type BaseClass() =
   // abstract method
   abstract member Add: int -> int -> int
   // abstract property
   abstract member Pi : float 

   // defaults
   default this.Add x y = x + y
   default this.Pi = 3.14 
```

你可以看到默认方法的定义方式与通常方式相同，只是使用`default`而不是`member`。

F# 与 C# 之间的一个主要区别是，在 C# 中，你可以使用`virtual`关键字将抽象定义和默认实现合并为一个单独的方法。在 F# 中，你不能这样做。你必须分别声明抽象方法和默认实现。`abstract member`有签名，`default`有实现。

### 抽象类

如果至少有一个抽象方法*没有*默认实现，则整个类都是抽象的，并且你必须通过为其添加`AbstractClass`属性来指示这一点。

```
[<AbstractClass>]
type AbstractBaseClass() =
   // abstract method
   abstract member Add: int -> int -> int

   // abstract immutable property
   abstract member Pi : float 

   // abstract read/write property
   abstract member Area : float with get,set 
```

如果这样做，那么编译器将不再抱怨缺少实现。

### 在子类中重写方法

要在子类中重写抽象方法或属性，使用`override`关键字而不是`member`关键字。除了这个变化，重写的方法是按照通常的方式定义的。

```
[<AbstractClass>]
type Animal() =
   abstract member MakeNoise: unit -> unit 

type Dog() =
   inherit Animal() 
   override this.MakeNoise () = printfn "woof"

// test
// let animal = new Animal()  // error creating ABC
let dog = new Dog()
dog.MakeNoise() 
```

要调用基方法，请使用`base`关键字，就像在 C# 中一样。

```
type Vehicle() =
   abstract member TopSpeed: unit -> int
   default this.TopSpeed() = 60

type Rocket() =
   inherit Vehicle() 
   override this.TopSpeed() = base.TopSpeed() * 10

// test
let vehicle = new Vehicle()
printfn "vehicle.TopSpeed = %i" <| vehicle.TopSpeed()
let rocket = new Rocket()
printfn "rocket.TopSpeed = %i" <| rocket.TopSpeed() 
```

### 抽象方法摘要

抽象方法基本上很简单，与 C# 类似。如果你习惯于 C#，可能有两个地方会有些棘手：

+   你必须理解函数签名如何工作以及它们的语法是什么！详细讨论请参阅函数签名帖子。

+   没有全能虚方法。你必须分别定义抽象方法和默认实现。

# 接口

# 接口

接口在 F# 中是可用且完全支持的，但在使用方式上有许多重要的区别，与你在 C# 中可能习惯的方式不同。

### 定义接口

定义接口与定义抽象类类似。事实上，它们非常相似，以至于你可能很容易混淆它们。

这是一个接口定义：

```
type MyInterface =
   // abstract method
   abstract member Add: int -> int -> int

   // abstract immutable property
   abstract member Pi : float 

   // abstract read/write property
   abstract member Area : float with get,set 
```

这里是等效抽象基类的定义：

```
[<AbstractClass>]
type AbstractBaseClass() =
   // abstract method
   abstract member Add: int -> int -> int

   // abstract immutable property
   abstract member Pi : float 

   // abstract read/write property
   abstract member Area : float with get,set 
```

那么区别在哪里呢？像往常一样，所有抽象成员仅由签名定义。唯一的区别似乎是缺少`[<AbstractClass>]`属性。

但在之前关于抽象方法的讨论中，我们强调了需要`[<AbstractClass>]`属性；否则编译器会抱怨方法没有实现。那么接口定义如何摆脱这一点呢？

答案很琐碎，但微妙。*接口没有构造函数*。也就是说，它在接口名后没有括号：

```
type MyInterface =   // <- no parens! 
```

就是这样。删除括号将类定义转换为接口！

### 显式和隐式接口实现

当在类中实现接口时，F# 与 C# 相比有很大不同。在 C# 中，你可以将接口列表添加到类定义中，并隐式实现接口。

F# 中并非如此。在 F# 中，所有接口必须*显式*实现。

在显式接口实现中，接口成员只能通过接口实例（例如通过将类转换为接口类型）访问。接口成员不作为类本身的一部分可见。

C#支持显式和隐式接口实现，但几乎总是使用隐式方法，并且许多程序员甚至不知道[C#中的显式接口](http://msdn.microsoft.com/en-us/library/ms173157.aspx)。

### 在 F#中实现接口

那么，如何在 F#中实现接口？你不能像继承抽象基类那样“继承”它。你必须为每个接口成员提供显式实现，使用语法`interface XXX with`，如下所示：

```
type IAddingService =
    abstract member Add: int -> int -> int

type MyAddingService() =

    interface IAddingService with 
        member this.Add x y = 
            x + y

    interface System.IDisposable with 
        member this.Dispose() = 
            printfn "disposed" 
```

上述代码展示了类`MyAddingService`如何显式实现`IAddingService`和`IDisposable`接口。在必需的`interface XXX with`部分之后，成员以正常方式实现。

（另外注意，`MyAddingService()`有一个构造函数，而`IAddingService`没有。）

### 使用接口

现在让我们尝试使用添加服务接口：

```
let mas = new MyAddingService()
mas.Add 1 2    // error 
```

立即，我们遇到了一个错误。似乎实例根本没有实现`Add`方法。当然，这实际上意味着我们必须首先使用`：>`运算符将其转换为接口：

```
// cast to the interface
let mas = new MyAddingService()
let adder = mas :> IAddingService
adder.Add 1 2  // ok 
```

这可能看起来非常笨拙，但实际上并不是问题，因为在大多数情况下，转换会隐式完成。

例如，你通常会将一个实例传递给指定接口参数的函数。在这种情况下，转换是自动完成的：

```
// function that requires an interface
let testAddingService (adder:IAddingService) = 
    printfn "1+2=%i" <| adder.Add 1 2  // ok

let mas = new MyAddingService()
testAddingService mas // cast automatically 
```

而在`IDisposable`的特殊情况下，`use`关键字也会根据需要自动转换实例：

```
let testDispose = 
    use mas = new MyAddingService()
    printfn "testing"
    // Dispose() is called here 
```

# 对象表达式

# 对象表达式

因此，正如我们在上一篇文章中所看到的那样，在 F#中实现接口比在 C#中更加笨拙。但是 F#有一个名为"对象表达式"的技巧。

使用对象表达式，你可以即时地实现一个接口，而不必创建一个类。

### 使用对象表达式实现接口

对象表达式最常用于实现接口。为此，你可以使用语法`new MyInterface with ...`，并将整个内容放在花括号中（这是 F#中的少数用途之一！）

这里是一些示例代码，创建了多个对象，每个对象都实现了`IDisposable`。

```
// create a new object that implements IDisposable
let makeResource name = 
   { new System.IDisposable 
     with member this.Dispose() = printfn "%s disposed" name }

let useAndDisposeResources = 
    use r1 = makeResource "first resource"
    printfn "using first resource" 
    for i in [1..3] do
        let resourceName = sprintf "\tinner resource %d" i
        use temp = makeResource resourceName 
        printfn "\tdo something with %s" resourceName 
    use r2 = makeResource "second resource"
    printfn "using second resource" 
    printfn "done." 
```

如果你执行此代码，你将看到下面的输出。你可以看到当对象超出范围时确实调用了`Dispose()`。

```
using first resource
    do something with   inner resource 1
    inner resource 1 disposed
    do something with   inner resource 2
    inner resource 2 disposed
    do something with   inner resource 3
    inner resource 3 disposed
using second resource
done.
second resource disposed
first resource disposed

```

我们也可以采用与`IAddingService`相同的方法，并且也可以即时创建一个。

```
let makeAdder id = 
   { new IAddingService with 
     member this.Add x y =
         printfn "Adder%i is adding" id 
         let result = x + y   
         printfn "%i + %i = %i" x y result 
         result 
         }

let testAdders = 
    for i in [1..3] do
        let adder = makeAdder i
        let result = adder.Add i i 
        () //ignore result 
```

对象表达式非常方便，如果你要与一个接口密集的库进行交互，可以大大减少你需要创建的类的数量。
