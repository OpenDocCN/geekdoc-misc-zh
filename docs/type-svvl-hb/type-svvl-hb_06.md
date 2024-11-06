# JavaScriptはTypeScriptの一部

> 原文：[`typescriptbook.jp/overview/javascript-is-typescript`](https://typescriptbook.jp/overview/javascript-is-typescript)

TypeScriptの文法はJavaScriptの文法を拡張したものです。TypeScriptで拡張された文法は、主に型に関する部分です。それ以外のほとんどの文法はJavaScriptに由来するものです。そのため、素のJavaScriptもTypeScriptとして扱うことができます。たとえば、次のコードは100%JavaScriptのものですが、これをTypeScriptコンパイラーは解析でき、静的な検査が行なえます。

```
js`const  <data-lsp lsp="const hello: &quot;Hello&quot;">hello</data-lsp>  =  "Hello";const  <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>  =  "World";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const hello: &quot;Hello&quot;">hello</data-lsp> +  " "  + <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>);"Hello World"`
```

```
js`const  <data-lsp lsp="const hello: &quot;Hello&quot;">hello</data-lsp>  =  "Hello";const  <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>  =  "World";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const hello: &quot;Hello&quot;">hello</data-lsp> +  " "  + <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>);"Hello World"`
```

TypeScriptから見ると、JavaScriptはTypeScriptの一部と言えます。そのため、TypeScriptを十分に理解するには、JavaScriptの理解が欠かせません。まだJavaScriptをよく分かっていない場合は、TypeScriptの学習と平行してJavaScriptも学ぶ必要があります。本書はTypeScript 入門者向けですが、TypeScriptの理解に欠かせないJavaScriptの文法や仕様についても同時に学べるようになっています。
