# コンパニオンオブジェクトパターン

> 原文：[`typescriptbook.jp/tips/companion-object`](https://typescriptbook.jp/tips/companion-object)

TypeScriptでは値と型に同名を与えてその両方を区別なく使うことができるテクニックがあります。これをコンパニオンオブジェクトと呼びます。

これは、クラスを作るほどでもなけどそれっぽいファクトリーメソッドとオブジェクトが欲しいときに重宝します。

## コンパニオンオブジェクト (Companion Object)​ への直接リンク")

次の例は長方形 (Rectangle) を作成するためのメソッド`from()`をもつオブジェクト`Rectangle`とその生成されるオブジェクトの型`Rectangle`です。これらの名称は衝突することなく定義ができ、外部から呼び出したときは同名で使用できます。

次の型と値 (ファクトリーメソッドを持つオブジェクト) は同じファイル`rectangle.ts`に存在するとします。

```
ts`export  type  <data-lsp lsp="type Rectangle = {
    height: number;
    width: number;
}">Rectangle</data-lsp>  = { <data-lsp lsp="(property) height: number">height</data-lsp>:  number; <data-lsp lsp="(property) width: number">width</data-lsp>:  number;};export  const  <data-lsp lsp="const Rectangle: {
    from(height: number, width: number): Rectangle;
}">Rectangle</data-lsp>  = {  <data-lsp lsp="(method) from(height: number, width: number): Rectangle">from</data-lsp>(<data-lsp lsp="(parameter) height: number">height</data-lsp>:  number, <data-lsp lsp="(parameter) width: number">width</data-lsp>:  number):  <data-lsp lsp="type Rectangle = {
    height: number;
    width: number;
}">Rectangle</data-lsp> {  return { <data-lsp lsp="(property) height: number">height</data-lsp>, <data-lsp lsp="(property) width: number">width</data-lsp>, }; },};`
```

```
ts`export  type <data-lsp lsp="type Rectangle = {
    height: number;
    width: number;
}">Rectangle</data-lsp> = { <data-lsp lsp="(property) height: number">height</data-lsp>:  number; <data-lsp lsp="(property) width: number">width</data-lsp>:  number;};export  const  <data-lsp lsp="const Rectangle: {
    from(height: number, width: number): Rectangle;
}">Rectangle</data-lsp>  = { <data-lsp lsp="(method) from(height: number, width: number): Rectangle">from</data-lsp>(<data-lsp lsp="(parameter) height: number">height</data-lsp>:  number, <data-lsp lsp="(parameter) width: number">width</data-lsp>:  number): <data-lsp lsp="type Rectangle = {
    height: number;
    width: number;
}">Rectangle</data-lsp> {  return { <data-lsp lsp="(property) height: number">height</data-lsp>, <data-lsp lsp="(property) width: number">width</data-lsp>, }; },};`
```

値も型も同名で定義します。これを外部から import してみます。

```
ts`import { <data-lsp lsp="(alias) type Rectangle = {
    height: number;
    width: number;
}
(alias) const Rectangle: {
    from(height: number, width: number): Rectangle;
}
import Rectangle">Rectangle</data-lsp> } from  "./rectangle";const  <data-lsp lsp="const rec: Rectangle">rec</data-lsp>:  <data-lsp lsp="(alias) type Rectangle = {
    height: number;
    width: number;
}
import Rectangle">Rectangle</data-lsp>  =  <data-lsp lsp="(alias) const Rectangle: {
    from(height: number, width: number): Rectangle;
}
import Rectangle">Rectangle</data-lsp>.<data-lsp lsp="(method) from(height: number, width: number): Rectangle">from</data-lsp>(1,  3);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rec: Rectangle">rec</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rec: Rectangle">rec</data-lsp>.<data-lsp lsp="(property) width: number">width</data-lsp>);3`
```

```
ts`import { <data-lsp lsp="(alias) type Rectangle = {
    height: number;
    width: number;
}
(alias) const Rectangle: {
    from(height: number, width: number): Rectangle;
}
import Rectangle">Rectangle</data-lsp> } from  "./rectangle";const  <data-lsp lsp="const rec: Rectangle">rec</data-lsp>: <data-lsp lsp="(alias) type Rectangle = {
    height: number;
    width: number;
}
import Rectangle">Rectangle</data-lsp> =  <data-lsp lsp="(alias) const Rectangle: {
    from(height: number, width: number): Rectangle;
}
import Rectangle">Rectangle</data-lsp>.<data-lsp lsp="(method) from(height: number, width: number): Rectangle">from</data-lsp>(1,  3);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rec: Rectangle">rec</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rec: Rectangle">rec</data-lsp>.<data-lsp lsp="(property) width: number">width</data-lsp>);3`
```

このように import の部分は`Rectangle`のみとなり見通しもつきやすいという特徴があります。ちなみに`Rectangle.from()`のRectangleが値であり`const rec: Rectangle`のRectangleが型です。このようにTypeScriptでは同名の値と型を同時に使うことができます。
