# TypeScript 不是什么？

> 原文：[`typescriptbook.jp/overview/typescript-is-not-that`](https://typescriptbook.jp/overview/typescript-is-not-that)

许多开发人员高度评价 TypeScript。在这种情况下，有些人过度高估了 TypeScript，这是一个误解。TypeScript 并不是一种魔法棒。本文将探讨 TypeScript 无法解决的问题。强迫 TypeScript 去做它无法做到的事情是徒劳的，因此理解这一点非常重要。

## 不会影响执行时的加速和内存节省​

经常在比较 TypeScript 和 JavaScript 时，会听到以下言论。

+   TypeScript 可以比 JavaScript 更快地执行

+   TypeScript 的内存消耗比 JavaScript 少

反过来，也有人担心以下情况。

+   TypeScript 是否比 JavaScript 编写慢？

+   TypeScript 的内存消耗是否比 JavaScript 大？

总的来说，TypeScript 的运行时性能与 JavaScript 相同。要理解这一点，需要牢记以下两个前提条件。

1.  TypeScript 没有运行时。

1.  TypeScript 编译器不进行优化。

### TypeScript 没有运行时​

TypeScript 没有运行时。这意味着，没有直接执行 TypeScript 的引擎。即使是开发 TypeScript 的 Microsoft 浏览器 Microsoft Edge，也无法执行 TypeScript。服务器端的 Node.js 也是如此^(1)。要执行用 TypeScript 编写的代码，必须先将其转换为 JavaScript 代码。因此，TypeScript 的性能取决于编译后的 JavaScript 代码。

### TypeScript 编译器不进行优化​

一般来说，“编译器”有三项工作。

1.  分析源代码并检查问题

1.  将源代码转换为另一种语言

1.  优化

    +   使执行速度更快

    +   使内存占用更少

    +   减少电力消耗

    +   减小执行文件的大小

其中，TypeScript 编译器只执行前两项。不会进行第三项优化。TypeScript 编译器基本上只是删除与类型相关的部分，其他部分几乎保持不变地转换为 JavaScript。

例如，编译以下 TypeScript 代码时，

```
TypeScriptコードts`const  <data-lsp lsp="const oneDay: number">oneDay</data-lsp>:  number  =  60  *  60  *  24;`
```

```
TypeScriptコードts`const  <data-lsp lsp="const oneDay: number">oneDay</data-lsp>:  number  =  60  *  60  *  24;`
```

生成的 JavaScript 代码如下。只是删除了类型注解中的`number`。

```
コンパイル後のJavaScriptコードjs`const  <data-lsp lsp="const oneDay: number">oneDay</data-lsp>  =  60  *  60  *  24;`
```

```
コンパイル後のJavaScriptコードjs`const  <data-lsp lsp="const oneDay: number">oneDay</data-lsp>  =  60  *  60  *  24;`
```

这个`60 * 60 * 24`的表达式可以在编译时静态计算。通过在编译时计算并生成下面这样的 JavaScript 代码，可以避免不必要的运行时计算。这有助于提高性能。

```
予め計算したJavaScriptコードjs`const  <data-lsp lsp="const oneDay: 86400">oneDay</data-lsp>  =  86400;`
```

```
予め計算したJavaScriptコードjs`const  <data-lsp lsp="const oneDay: 86400">oneDay</data-lsp>  =  86400;`
```

技术上，像上面这样的优化应该是可能的。但是，TypeScript 基本上不会进行这样的优化。TypeScript 编译器基本上只是去掉类型。

### 两者的性能基本相同​

我们已经看到 TypeScript 具有以下特点。

1.  TypeScript 没有运行时。

1.  TypeScript 编译器不进行优化。

由于这两个特点，当将完全相同的逻辑代码用 TypeScript 和 JavaScript 编写并进行比较时，它们之间的性能差异不足以引起注意^(2)。

## 不修复 JavaScript 的规范错误​

JavaScript 中本来是一个错误的规范已经变成了例子。例如，检查值的类型的 typeof 运算符会返回`"object"`，如果传入`null`。这被认为是一个错误，但为了向后兼容性，它被保留为规范。

```
js`typeof  null;"object"`
```

```
js`typeof  null;"object"`
```

即使是 TypeScript，这些规范错误也没有被修复。原因是，TypeScript 只是一种在 JavaScript 基础上添加类型的语言。

##### 学习分享

TypeScript 无法解决的问题

・改善 JavaScript 的运行时性能

・解决 JS 的规范错误

『サバイバルTypeScript』より

[分享此内容](https://twitter.com/intent/tweet?text=TypeScript%E3%81%8C%E8%A7%A3%E6%B1%BA%E3%81%97%E3%81%AA%E3%81%84%E3%81%93%E3%81%A8%0A%0A%E3%83%BBJavaScript%E3%81%AE%E5%AE%9F%E8%A1%8C%E6%99%82%E3%83%91%E3%83%95%E3%82%A9%E3%83%BC%E3%83%9E%E3%83%B3%E3%82%B9%E6%94%B9%E5%96%84%0A%E3%83%BBJS%E3%81%AE%E4%BB%95%E6%A7%98%E3%83%90%E3%82%B0%E3%81%AE%E8%A7%A3%E6%B1%BA%0A%0A%E3%80%8E%E3%82%B5%E3%83%90%E3%82%A4%E3%83%90%E3%83%ABTypeScript%E3%80%8F%E3%82%88%E3%82%8A)

* * *

1.  存在声称自己是 TypeScript 运行时的 Deno 服务器环境。即使是这样的 Deno，也会将 TypeScript 内部编译为 JavaScript，并在 JavaScript 引擎上执行。↩

1.  厳密に言うと、コンパイラオプション`target`を`es3`(古いJavaScript)に指定するなどで、「単に型を消すだけ」のコンパイルではなくなる場合もあるので常に同等が保証されているわけではありません。↩
