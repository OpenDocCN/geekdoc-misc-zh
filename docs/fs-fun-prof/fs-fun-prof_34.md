# 十个不使用静态类型函数式编程语言的理由

# 十个不使用静态类型函数式编程语言的理由

你是否对所有关于函数式编程的炒作感到厌倦？我也是！我想抱怨一些像我们这样理智的人应该远离它的原因。

[我想明确指出，当我说“静态类型函数式编程语言”时，我指的是还包括诸如类型推断、默认不可变性等内容的语言。实际上，这意味着 Haskell 和 ML 系列（包括 OCaml 和 F＃）。]

## 第一个原因：我不想追随最新的潮流

和大多数程序员一样，我天生保守，不喜欢学习新东西。这就是为什么我选择了 IT 职业。

我不会因为所有“酷毙了的小孩”都在做某件事而跟风——我会等到事情成熟，我可以获得一些清晰的看法。

对我来说，函数式编程还没有存在足够长的时间来说服我它是值得信赖的。

是的，我想有些古板的人可能会声称[ML](http://en.wikipedia.org/wiki/ML_\(programming_language\))和[Haskell](http://en.wikipedia.org/wiki/Haskell_\(programming_language\))已经存在了几乎和 Java 和 PHP 等老牌语言一样长的时间，但我最近才听说 Haskell，所以这个论点对我来说并不成立。

看看这些新人中最年轻的[F#](http://fsharp.org/)。它只有七岁，天哪！当然，对于地质学家来说，七年可能是很长的时间，但在互联网时间里，七年只是一眨眼的工夫。

所以，总的来说，我肯定会采取谨慎的态度，等待几十年，看看这个函数式编程的东西是否会持续存在，或者它只是昙花一现。

## 第二个原因：我按行数计费

我不知道你是怎么想的，但我写的代码行数越多，我就感到越有生产力。如果我一天可以输出 500 行代码，那就是干得好。我的提交很大，我的老板可以看到我一直很忙。

但是当我比较用函数式语言编写的代码和一个好老的类 C 语言时，代码量就少得多，这让我感到害怕。

我的意思是，看看用熟悉的语言编写的这段代码：

```
public static class SumOfSquaresHelper
{
   public static int Square(int i) {
      return i * i;
   }

   public static int SumOfSquares(int n) {
      int sum = 0;
      for (int i = 1; i <= n; i++)
      {
         sum += Square(i);
      }
      return sum;
   }
} 
```

并将其与此进行比较：

```
let square x = x * x
let sumOfSquares n = [1..n] |> List.map square |> List.sum 
```

17 行对比仅 2 行。[想象一下这种差异在整个项目中被放大的情况！](http://fpbridge.co.uk/why-fsharp.html#conciseness)

如果我采用这种方法，我的生产力将急剧下降。很抱歉——我实在承受不起。

## 第三个原因：我喜欢大括号

这还有另一件事。那些去掉大括号的语言到底怎么回事？他们怎么能称自己为真正的编程语言？

我会向你展示我说的是什么意思。这里是一个用熟悉的大括号编写的代码示例。

```
public class Squarer
{
    public int Square(int input) {
        var result = input * input;
        return result;
    }

    public void PrintSquare(int input) {
        var result = this.Square(input);
        Console.WriteLine("Input={0}. Result={1}", input, result);
    }
} 
```

这里有一些类似的代码，但没有大括号。

```
type Squarer() =  

    let Square input = 
        let result = input * input
        result

    let PrintSquare input = 
        let result = Square input
        printf "Input=%i. Result=%i" input result 
```

看看这个差异！我不知道你是怎么想的，但我觉得第二个例子有点让人不安，好像缺少了一些重要的东西。

老实说，没有花括号给予我的指导，我感到有点迷失。

## 理由 4：我喜欢看到显式类型

函数式语言的支持者声称，类型推断使代码更清晰，因为你不必一直在代码中添加类型声明。

嗯，碰巧我*喜欢*看到类型声明。如果我不知道每个参数的确切类型，我会感到不舒服。这就是为什么 [Java](http://steve-yegge.blogspot.co.uk/2006/03/execution-in-kingdom-of-nouns.html) 是我最喜欢的语言。

这是一些类似 ML 代码的函数签名。不需要类型声明，所有类型都会自动推断。

```
let GroupBy source keySelector = 
    ... 
```

这是 C# 中类似代码的函数签名，带有显式类型声明。

```
public IEnumerable<IGrouping<TKey, TSource>> GroupBy<TSource, TKey>(
    IEnumerable<TSource> source,
    Func<TSource, TKey> keySelector
    )
    ... 
```

在这一点上，我可能是少数人，但我更喜欢第二个版本。对我来说，知道返回的类型是 `IEnumerable<IGrouping<TKey, TSource>>` 很重要。

当然，编译器会为你检查类型并在类型不匹配时提醒你。但是为什么要让编译器做这个工作，当你的大脑可以做到呢？

好吧，我承认如果你确实使用了泛型，和 lambda 表达式，以及返回函数的函数，以及所有其他新潮的东西，那么是的，你的类型声明会变得非常复杂和复杂。并且很难正确地输入它们。

但是我有一个简单的解决方法 -- 不要使用泛型，也不要传递函数。你的签名会简单得多。

## 理由 5：我喜欢修复 bug

对我来说，没有什么能比得上发现和消灭一个讨厌的 bug 的刺激。如果 bug 出现在生产系统中，那就更好，因为这样我还会成为一个英雄。

但是[我读到](https://web.archive.org/web/20130918053426/http://www.simontylercousins.net/journal/2013/3/7/why-bugs-dont-like-f.html)在静态类型的函数式语言中，引入 bug 要困难得多。

这真是个令人沮丧的事情。

## 理由 6：我生活在调试器中

谈到修复 bug，我大部分时间都在调试器中度过，逐步执行代码。是的，我知道我应该使用单元测试，但说起来容易，做起来难，好吗？

无论如何，显然使用这些静态类型的函数式语言，[如果你的代码编译通过，它通常就能工作](http://www.haskell.org/haskellwiki/Why_Haskell_just_works)。

我被告知你必须花费大量时间来确保类型匹配，但是一旦完成了，代码编译成功后，就没有什么需要调试的了。那有什么乐趣呢？

这让我想到...

## 理由 7：我不想考虑每一个细节

匹配类型和确保一切完美听起来对我来说很累人。

实际上，我听说你被迫考虑所有可能的边界情况，所有可能的错误条件，以及其他任何可能出错的事情。而且你必须在一开始就做到这一点 -- 你不能偷懒，把它推迟到以后。

我宁愿先让一切（大部分）按照正常路径工作，然后在问题出现时修复错误。

## 理由 8：我喜欢检查空值

我非常注意在每个方法上[检查空值](http://stackoverflow.com/questions/7585493/null-parameter-checking-in-c-sharp)。因此，知道我的代码完全无懈可击让我感到非常满足。

```
void someMethod(SomeClass x) {
    if (x == null) { throw new NullArgumentException(); }

    x.doSomething();
} 
```

哈哈！开玩笑！我当然不会费心到处放置空值检查代码。我永远不会完成任何真正的工作。

但我只遇到过一次由 NPE 引起的严重崩溃。在我花了几个星期寻找问题期间，企业并没有损失太多钱。所以我不确定为什么这是一个[大问题](http://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare)。

## 理由 9：我喜欢在任何地方使用设计模式

我首先在[设计模式书籍](http://www.amazon.com/First-Design-Patterns-Elisabeth-Freeman/dp/0596007124)中了解到设计模式（由于某种原因它被称为四人帮书，但我不确定原因），自那以后，我一直努力在所有问题上都使用它们。这确实让我的代码看起来严肃而“企业化”，并且让我的老板印象深刻。

但我没有看到函数式设计中提到模式。你怎么可能在没有 Strategy、AbstractFactory、Decorator、Proxy 等的情况下完成有用的工作？

或许函数式程序员不知道它们的存在？

## 理由 10：这太数学化了

这里有一些用于计算平方和的代码。由于其中所有奇怪的符号，这太难理解了。

```
ss=: +/ @: *: 
```

糟糕，抱歉！我的错。那是[J 语言](http://en.wikipedia.org/wiki/J_\(programming_language\))。

但我听说函数式程序使用奇怪的符号像`<*>`和`>>=`以及名为“monads”和“functors”的模糊概念。

我不知道为什么函数式的人们不能坚持我已经了解的事物——明显的符号像`++`和`!=`以及易于理解的概念如“继承”和“多态性”。

## 总结：我不明白

你知道吗。我不明白。我不明白函数式编程有什么用处。

我真正想要的是，有人能够在单个页面上展示一些真正的好处，而不是给我太多信息。

更新：所以现在我已经阅读了“一个页面上你需要知道的一切”的页面。但对我来说太简短和简单了。

我真的想要一些更深入的东西——一些我能够深入研究的东西。

不，不要说我应该阅读[教程](http://learnyouahaskell.com/)，并且[尝试示例](http://www.tryfsharp.org/Learn)，以及编写自己的代码。我只是想要理解它而不必做所有这些工作。

我不想要为了学习新范例而[改变我的思维方式](https://web.archive.org/web/20140118170751/http://dave.fayr.am/posts/2011-08-19-lets-go-shopping.html)。
