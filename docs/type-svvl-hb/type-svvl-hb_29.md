# import、export、require

> 原文：[`typescriptbook.jp/reference/import-export-require`](https://typescriptbook.jp/reference/import-export-require)

在实际工作中，通常会将多个 JavaScript 文件组合在一起，构成一个应用程序。这就是所谓的模块化开发。这里将解释 JavaScript 和 TypeScript 中的模块，以及如何组合模块的`import`、`export`、`require`。

## 脚本和模块​

JavaScript 文件大致分为脚本和模块两类。脚本就是普通的 JavaScript 文件。

```
スクリプトjs`const  <data-lsp lsp="const foo: &quot;foo&quot;">foo</data-lsp>  =  "foo";`
```

```
スクリプトjs`const  <data-lsp lsp="const foo: &quot;foo&quot;">foo</data-lsp>  =  "foo";`
```

模块是指包含一个或多个`import`或`export`的 JavaScript 文件。`import`是从其他模块导入变量、函数、类等的关键字。`export`是用于向其他模块公开变量、函数、类等的关键字。

```
モジュールjs`export  const  <data-lsp lsp="const foo: &quot;foo&quot;">foo</data-lsp>  =  "foo";`
```

```
モジュールjs`export  const  <data-lsp lsp="const foo: &quot;foo&quot;">foo</data-lsp>  =  "foo";`
```

因此，即使以前的脚本文件没有`import`或`export`，添加后，它也会变成模块文件。

## 値の公開と非公開​

JavaScript 模块只会公开带有`export`的值，其他模块可以引用这些值。例如，下面的`publicValue`可以被其他模块使用。而`privateValue`则无法被外部使用。

```
js`export  const  <data-lsp lsp="const publicValue: 1">publicValue</data-lsp>  =  1;const  <data-lsp lsp="const privateValue: 2">privateValue</data-lsp>  =  2;`
```

```
js`export  const  <data-lsp lsp="const publicValue: 1">publicValue</data-lsp>  =  1;const  <data-lsp lsp="const privateValue: 2">privateValue</data-lsp>  =  2;`
```

在 JavaScript 模块中，默认情况下，变量和函数等都是私有的。在其他语言如 Java 中，模块（包）的成员默认是公开的，需要将要私有的内容标记为`private`。与这些语言相比，JavaScript 的基本策略完全相反，需要注意。

## モジュールは常にstrict mode​

モジュール的 JavaScript 会一直处于 strict mode。在 strict mode 下，各种危险的代码写法都会被禁止。例如，对未定义变量的赋值会导致错误。

```
js`<data-lsp lsp="any">foo</data-lsp> =  1; // 未定義の変数 fooへの代入 ReferenceError: foo is not definedexport  const  <data-lsp lsp="const bar: any">bar</data-lsp>  = <data-lsp lsp="any">foo</data-lsp>;`
```

```
js`<data-lsp lsp="any">foo</data-lsp> =  1; // 未定義の変数 fooへの代入 ReferenceError: foo is not definedexport  const  <data-lsp lsp="const bar: any">bar</data-lsp>  = <data-lsp lsp="any">foo</data-lsp>;`
```

## 模块在`import`时只会被评估一次​

模块的代码只会在第一次`import`时被评估。在第二次及以后的`import`中，会使用最初评估的内容。换句话说，模块在第一次`import`时就被缓存了，也可以说模块是一种单例。

例如，假设三次读取名为`module.js`的模块，那么`module.js`只会在第一次评估时执行。

```
module.jsjs`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("モジュールを評価しています");// このログが出力されるのは1 回だけexport  const  <data-lsp lsp="const value: 1">value</data-lsp>  =  1;`
```

```
module.jsjs`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("モジュールを評価しています");// このログが出力されるのは1 回だけexport  const  <data-lsp lsp="const value: 1">value</data-lsp>  =  1;`
```

```
main.jsjs`import  "./module.js";"モジュールを評価しています"import  "./module.js";import  "./module.js";`
```

```
main.jsjs`import  "./module.js";"モジュールを評価しています"import  "./module.js";import  "./module.js";`
```

## 模块的历史​

### 以前的 JavaScript​

以前 JavaScript 只能在浏览器中运行，虽然有模块分割的概念，但那只是在浏览器中，甚至是在`html`中管理。如果有一个常用的包叫做`jQuery`，那么需要在`html`中这样写。

```
`<script src="https://ajax.googleapis.com/ajax/libs/jquery/x.y.z/jquery.min.js"></script>`
```

```
`<script src="https://ajax.googleapis.com/ajax/libs/jquery/x.y.z/jquery.min.js"></script>`
```

如果有依赖于`jQuery`的包，那么必须将其声明放在`jQuery`之后。

```
`<script src="https://ajax.googleapis.com/ajax/libs/jqueryui/x.y.z/jquery-ui.min.js"></script>`
```

```
`<script src="https://ajax.googleapis.com/ajax/libs/jqueryui/x.y.z/jquery-ui.min.js"></script>`
```

如果包很少，还好，但随着包的增多，依赖关系会变得复杂。如果导入顺序错误，那么`html`可能就无法正常运行。

### Node.js 的出现​

自`npm`出现以来，主流变成了直接获取想要的包并直接使用。

## `CommonJS`​

### `require()`​

Node.js 仍然支持读取其他`.js`文件（TypeScript 也支持`.ts`）。基本语法如下。

```
ts`const  <data-lsp lsp="const package1: any">package1</data-lsp>  =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("package1");`
```

```
ts`const  <data-lsp lsp="const package1: any">package1</data-lsp>  = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("package1");`
```

这意味着将`package1`包的内容导入到常量`package1`中。此时，`package1`必须存在于当前项目的`node_modules`目录中（除非是内置库）。

也可以加载自己创建的其他`.js, .ts`文件。在调用文件中，使用**相对路径**指定要加载的文件位置。即使在同一级别，也必须使用相对路径。在这种情况下，可以省略`.js, .json`，并且在 TypeScript 开发中，考虑到最终会编译为 JavaScript，最好不要写这些后缀。

```
ts`const  <data-lsp lsp="const myPackage: any">myPackage</data-lsp>  =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./MyPackage");`
```

```
ts`const  <data-lsp lsp="const myPackage: any">myPackage</data-lsp>  = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./MyPackage");`
```

如果将`.js`输出到与`.ts`相同的位置，那么对于 TypeScript 来说，会存在两个同名文件，TypeScript 会优先读取`.js`，请注意。如果即使更改了 TypeScript 代码，但似乎没有应用更改，则可能存在这个问题。

如果指定的路径是一个目录，并且其中有`index.js(index.ts)`文件，只需写出目录名，就会自动加载`index.js(index.ts)`。

### `module.exports`​

要读取其他文件，该文件必须输出内容。为此，使用以下语法。

```
increment.jsts`<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
increment.jsts`<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

如果有一个名为`.js`的文件，想要在同一级别下加载它，可以这样做。

```
index.jsts`const  <data-lsp lsp="const increment: any">increment</data-lsp>  =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./increment");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));`
```

```
index.jsts`const  <data-lsp lsp="const increment: any">increment</data-lsp>  = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./increment");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));`
```

在这种情况下，接收导入内容的常���`increment`不一定要使用这个名称，可以更改。

この`module.exports`はひとつのファイルでいくらでも書くことができますが、適用されるのは最後のもののみです。

```
dayOfWeek.jsts`<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Monday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Tuesday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Wednesday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Thursday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Friday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Saturday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Sunday";`
```

```
dayOfWeek.jsts`<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Monday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Tuesday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Wednesday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Thursday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Friday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Saturday";<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  =  "Sunday";`
```

```
index.jsts`const  <data-lsp lsp="const day: any">day</data-lsp>  =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./dayOfWeek");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const day: any">day</data-lsp>);'Sunday'`
```

```
index.jsts`const  <data-lsp lsp="const day: any">day</data-lsp>  = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./dayOfWeek");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const day: any">day</data-lsp>);'Sunday'`
```

### `exports`​

`module.exports`だと良くも悪くも出力しているものの名前を変更できてしまいます。それを避けたい時はこの`exports`を使用します。

```
util.jsts`<data-lsp lsp="var exports: any">exports</data-lsp>.<data-lsp lsp="any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
util.jsts`<data-lsp lsp="var exports: any">exports</data-lsp>.<data-lsp lsp="any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

読み込み側では次のようになります。

```
index.jsts`const  <data-lsp lsp="const util: any">util</data-lsp>  =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const util: any">util</data-lsp>.<data-lsp lsp="any">increment</data-lsp>(3));4`
```

```
index.jsts`const  <data-lsp lsp="const util: any">util</data-lsp>  = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const util: any">util</data-lsp>.<data-lsp lsp="any">increment</data-lsp>(3));4`
```

分割代入を使うこともできます。

```
index.jsts`const { <data-lsp lsp="const increment: any">increment</data-lsp> } =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));4`
```

```
index.jsts`const { <data-lsp lsp="const increment: any">increment</data-lsp> } = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));4`
```

こちらは`increment`という名前で使用する必要があります。他のファイルに同じ名前のものがあり、名前を変更する必要がある時は、分割代入のときと同じように名前を変更することができます。

```
index.jsts`const { <data-lsp lsp="const increment: any">increment</data-lsp> } =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./other");const { <data-lsp lsp="any">increment</data-lsp>: <data-lsp lsp="const inc: any">inc</data-lsp> } =  <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const inc: any">inc</data-lsp>(3));4`
```

```
index.jsts`const { <data-lsp lsp="const increment: any">increment</data-lsp> } = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./other");const { <data-lsp lsp="any">increment</data-lsp>: <data-lsp lsp="const inc: any">inc</data-lsp> } = <data-lsp lsp="var require: NodeRequire
(id: string) => any">require</data-lsp>("./util");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const inc: any">inc</data-lsp>(3));4`
```

## `ES Module`​

主にフロントエンド(ブラウザ)で採用��れているファイルの読み込み方法です。`ES6`で追加された機能のため、あまりにも古いブラウザでは動作しません。

### `import`​

`require()`と同じく他の`.js, .ts`ファイルを読み込む機能ですが、`require()`はファイル内のどこにでも書くことができる一方で`import`は**必ずファイルの一番上に書く必要があります**。

なお、書き方が2 通りあります。

```
ts`import  *  as package1 from  "package1";import package2 from  "package2";`
```

```
ts`import  *  as package1 from  "package1";import package2 from  "package2";`
```

使い方に若干差がありますので以下で説明します。

### `export default`​

`module.exports`に対応するものです。`module.exports`と異なりひとつのファイルはひとつの`export default`しか許されていなく複数書くと動作しません。

```
increment.jsts`export  default (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
increment.jsts`export  default (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

この`.js`のファイルは次のようにして読み込みます。

```
index.jsts`import <data-lsp lsp="import increment">increment</data-lsp> from  "./increment";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: number): number
import increment">increment</data-lsp>(3));4`
```

```
index.jsts`import <data-lsp lsp="import increment">increment</data-lsp> from  "./increment";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: number): number
import increment">increment</data-lsp>(3));4`
```

```
index.jsts`import  *  as <data-lsp lsp="import increment">increment</data-lsp> from  "./increment";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import increment">increment</data-lsp>.<data-lsp lsp="(property) default: (i: number) => number">default</data-lsp>(3));4`
```

```
index.jsts`import  *  as <data-lsp lsp="import increment">increment</data-lsp> from  "./increment";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import increment">increment</data-lsp>.<data-lsp lsp="(property) default: (i: number) => number">default</data-lsp>(3));4`
```

### `export`​

`exports`に相当するものです。書き方が2 通りあります。

```
util.jsts`export  const  <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
util.jsts`export  const <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
util.jsts`const  <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;export { <data-lsp lsp="(alias) const increment: (i: any) => any
export increment">increment</data-lsp> };`
```

```
util.jsts`const <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;export { <data-lsp lsp="(alias) const increment: (i: any) => any
export increment">increment</data-lsp> };`
```

なお1 番目の表記は定数宣言の`const`を使っていますが`let`を使っても読み込み側から定義されている`increment`を書き換えることはできません。

次のようにして読み込みます。

```
index.jsts`import { <data-lsp lsp="(alias) const increment: (i: number) => number
import increment">increment</data-lsp> } from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: number): number
import increment">increment</data-lsp>(3));4`
```

```
index.jsts`import { <data-lsp lsp="(alias) const increment: (i: number) => number
import increment">increment</data-lsp> } from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: number): number
import increment">increment</data-lsp>(3));4`
```

```
index.jsts`import  *  as <data-lsp lsp="import util">util</data-lsp> from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import util">util</data-lsp>.<data-lsp lsp="const increment: (i: number) => number">increment</data-lsp>(3));4`
```

```
index.jsts`import  *  as <data-lsp lsp="import util">util</data-lsp> from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import util">util</data-lsp>.<data-lsp lsp="const increment: (i: number) => number">increment</data-lsp>(3));4`
```

1 番目の場合の`import`で名前を変更するときは、`require`のとき(分割代入)と異なり`as`という表記を使って変更します。

```
index.jsts`import { <data-lsp lsp="const increment: (i: number) => number">increment</data-lsp> as <data-lsp lsp="(alias) const inc: (i: number) => number
import inc">inc</data-lsp> } from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) inc(i: number): number
import inc">inc</data-lsp>(3));4`
```

```
index.jsts`import { <data-lsp lsp="const increment: (i: number) => number">increment</data-lsp> as <data-lsp lsp="(alias) const inc: (i: number) => number
import inc">inc</data-lsp> } from  "./util";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) inc(i: number): number
import inc">inc</data-lsp>(3));4`
```

### `import()`​

`ES Module`では`import`をファイルの先頭に書く必要があります。これは動的に読み込むファイルを切り替えられないことを意味します。この`import()`はその代替手段にあたります。

`require()`と異なる点としては`import()`はモジュールの読み込みを非同期で行います。つまり`Promise`を返します。

```
index.jsts`import("./util").<data-lsp lsp="(method) Promise<typeof import(&quot;/vercel/path0/util&quot;)>.then<void, never>(onfulfilled?: ((value: typeof import(&quot;/vercel/path0/util&quot;)) => void | PromiseLike<void>) | null | undefined, onrejected?: ((reason: any) => PromiseLike<never>) | null | undefined): Promise<...>">then</data-lsp>(({ <data-lsp lsp="(parameter) increment: (i: number) => number">increment</data-lsp> }) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) increment: (i: number) => number">increment</data-lsp>(3));  // @log: 4});`
```

```
index.jsts`import("./util").<data-lsp lsp="(method) Promise<typeof import(&quot;/vercel/path0/util&quot;)>.then<void, never>(onfulfilled?: ((value: typeof import(&quot;/vercel/path0/util&quot;)) => void | PromiseLike<void>) | null | undefined, onrejected?: ((reason: any) => PromiseLike<never>) | null | undefined): Promise<...>">then</data-lsp>(({ <data-lsp lsp="(parameter) increment: (i: number) => number">increment</data-lsp> }) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) increment: (i: number) => number">increment</data-lsp>(3));  // @log: 4});`
```

## Node.jsで`ES Module`を使う​

先述のとおりNode.jsでは`CommonJS`が長く使われていますが、`13.2.0`でついに正式に`ES Module`もサポートされました。

しかしながら、あくまでもNode.jsは`CommonJS`で動作することが前提なので`ES Module`を使いたい時はすこし準備が必要になります。

### `.mjs`​

`ES Module`として動作させたいJavaScriptのファイルをすべて`.mjs`の拡張子に変更します。

```
increment.mjsts`export  const  <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
increment.mjsts`export  const <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

読み込み側は以下です。

```
index.mjsts`import { <data-lsp lsp="import increment">increment</data-lsp> } from  "./increment.mjs";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import increment">increment</data-lsp>(3));4`
```

```
index.mjsts`import { <data-lsp lsp="import increment">increment</data-lsp> } from  "./increment.mjs";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="import increment">increment</data-lsp>(3));4`
```

`import`で使うファイルの**拡張子が省略できない**ことに注意してください。

### `"type": "module"`​

`package.json`にこの記述を追加するとパッケージ全体が`ES Module`をサポートします。

```
json`{  "name":  "YYTS",  "version":  "1.0.0",  "main":  "index.js",  "type":  "module",  "license":  "Apache-2.0"}`
```

```
json`{  "name":  "YYTS",  "version":  "1.0.0",  "main":  "index.js",  "type":  "module",  "license":  "Apache-2.0"}`
```

このようにすることで拡張子を`.mjs`に変更しなくてもそのまま`.js`で`ES Module`を使えるようになります。なお`"type": "module"`の省略時は`"type": "commonjs"`と指定されたとみなされます。これは今までどおりのNode.jsです。

```
increment.jsts`export  const  <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
increment.jsts`export  const <data-lsp lsp="const increment: (i: any) => any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
index.jsts`import { <data-lsp lsp="(alias) const increment: (i: any) => any
import increment">increment</data-lsp> } from  "./increment.js";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: any): any
import increment">increment</data-lsp>(3));4`
```

```
index.jsts`import { <data-lsp lsp="(alias) const increment: (i: any) => any
import increment">increment</data-lsp> } from  "./increment.js";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) increment(i: any): any
import increment">increment</data-lsp>(3));4`
```

`.js`ではありますが**読み込む時は拡張子を省略できなくなる**ことに注意してください。

#### `.cjs`​

`CommonJS`で書かれたJavaScriptを読み込みたくなったときは`CommonJS`で書かれているファイルをすべて`.cjs`に変更する必要があります。

```
increment.cjsts`<data-lsp lsp="var exports: any">exports</data-lsp>.<data-lsp lsp="any">increment</data-lsp>  = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

```
increment.cjsts`<data-lsp lsp="var exports: any">exports</data-lsp>.<data-lsp lsp="any">increment</data-lsp> = (<data-lsp lsp="(parameter) i: any">i</data-lsp>) => <data-lsp lsp="(parameter) i: any">i</data-lsp> +  1;`
```

読み込み側は次のようになります。

```
index.jsts`import { <data-lsp lsp="(alias) (method) createRequire(path: string | URL): NodeRequire
import createRequire">createRequire</data-lsp> } from  "module";const  <data-lsp lsp="const require: NodeRequire">require</data-lsp>  =  <data-lsp lsp="(alias) createRequire(path: string | URL): NodeRequire
import createRequire">createRequire</data-lsp>(import.<data-lsp lsp="" style="border-bottom:solid 2px lightgrey">meta</data-lsp>.<data-lsp lsp="(property) ImportMeta.url: string">url</data-lsp>);const { <data-lsp lsp="const increment: any">increment</data-lsp> } =  <data-lsp lsp="const require: NodeRequire
(id: string) => any">require</data-lsp>("./increment.cjs");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));4`
```

```
index.jsts`import { <data-lsp lsp="(alias) (method) createRequire(path: string | URL): NodeRequire
import createRequire">createRequire</data-lsp> } from  "module";const  <data-lsp lsp="const require: NodeRequire">require</data-lsp>  = <data-lsp lsp="(alias) createRequire(path: string | URL): NodeRequire
import createRequire">createRequire</data-lsp>(import.<data-lsp lsp="" style="border-bottom:solid 2px lightgrey">meta</data-lsp>.<data-lsp lsp="(property) ImportMeta.url: string">url</data-lsp>);const { <data-lsp lsp="const increment: any">increment</data-lsp> } = <data-lsp lsp="const require: NodeRequire
(id: string) => any">require</data-lsp>("./increment.cjs");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const increment: any">increment</data-lsp>(3));4`
```

`ES Module`には`require()`がなく、一手間加えて作り出す必要があります。

### `"type": "module"`の問題点​

すべてを`ES Module`として読み込むこの設定は、多くのパッケージがまだ`"type": "module"`に対応していない現状としては非常に使いづらいです。

たとえば`linter`やテストといった各種開発補助のパッケージの設定ファイルを`.js`で書いていると動作しなくなってしまいます。かといってこれらを`.cjs`に書き換えても、パッケージが設定ファイルの読み込み規則に`.cjs`が含んでいなければそれらのパッケージは設定ファイルがないと見なします。そのため`"type": "module"`は現段階では扱いづらいものとなっています。

## TypeScriptでは​

TypeScriptでは一般的に`ES Module`方式に則った記法で書きます。これは`CommonJS`を使用しないというわけではなく、コンパイル時の設定で`CommonJS, ES Module`のどちらにも対応した形式で出力できるのであまり問題はありません。ここまでの経緯などはTypeScriptでは意識することがあまりないでしょう。

また、執筆時(2021/01)ではTypeScriptのコンパイルは`.js`のみを出力でき`.cjs, .mjs`を出力する設定はありません。ブラウザでもサーバーでも使えるJavaScriptを出力したい場合は一手間加える必要があります。

出力の方法に関してはtsconfig.jsonのページに説明がありますのでそちらをご覧ください。

## 📄️ tsconfig.jsonを設定する

Node.jsはそれ自身ではTypeScriptをサポートしているわけではないため、TypeScriptの導入をする時はTypeScriptの設定ファイルであるtsconfig.jsonが必要です。

## `require? import?`​

ブラウザ用、サーバー用の用途で使い分けてください。ブラウザ用であれば`ES Module`を、サーバー用であれば`CommonJS`が無難な選択肢になります。どちらでも使えるユニバーサルなパッケージであればDual Packageを目指すのもよいでしょう。

## 📄️ デュアルパッケージ開発者のためのtsconfig

フロントエンドでもバックエンドでもTypeScriptこれ一本！Universal JSという考えがあります。確かにフロントエンドを動的にしたいのであればほぼ避けて通れないJavaScriptと、バックエンドでも使えるようになったJavaScriptで同じコードを使いまわせれば保守の観点でも異なる言語を触る必要がなくなり、統一言語としての価値が大いにあります。

## `default export? named export?`​

`module.exports`と`export default`はdefault exportと呼ばれ、`exports`と`export`はnamed exportと呼ばれています。どちらも長所と短所があり、たびたび議論になる話題です。どちらか一方を使うように統一するコーディングガイドを持っている企業もあるようですが、どちらかが極端に多いというわけでもないので好みの範疇です。

### default export​

#### default exportのPros​

+   `import`する時に名前を変えることができる

+   そのファイルが他の`export`に比べ何をもっとも提供したいのかがわかる

#### default exportのCons​

+   エディター、IDEによっては入力補完が効きづらい

+   再エクスポートの際に名前をつける必要がある

### named export​

#### named exportのPros​

+   エディター、IDEによる入力補完が効く

+   ひとつのファイルから複数`export`できる

#### named exportのCons​

+   (名前の変更はできるものの)基本的に決まった名前で`import`して使う必要がある

+   `export`しているファイルが名前を変更すると動作しなくなる

ここで挙がっている**名前を変えることができる**についてはいろいろな意見があります。

### ファイルが提供したいもの​

たとえばある国の会計ソフトウェアを作っていたとして、その国の消費税が8%だったとします。そのときのあるファイルの`export`はこのようになっていました。

```
taxIncluded.tsts`export  default (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.08;`
```

```
taxIncluded.tsts`export  default (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.08;`
```

もちろん呼び出し側はそのまま使うことができます。

```
index.tsts`import <data-lsp lsp="import taxIncluded">taxIncluded</data-lsp> from  "./taxIncluded";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncluded(i: number): number
import taxIncluded">taxIncluded</data-lsp>(100));108`
```

```
index.tsts`import <data-lsp lsp="import taxIncluded">taxIncluded</data-lsp> from  "./taxIncluded";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncluded(i: number): number
import taxIncluded">taxIncluded</data-lsp>(100));108`
```

ここで、ある国が消費税を10%に変更したとします。このときこのシステムでは`taxIncluded.ts`を変更すればこと足ります。

```
taxIncluded.tsts`export  default (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.1;`
```

```
taxIncluded.tsts`export  default (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.1;`
```

この変更をこのファイル以外は知る必要がありませんし、知ることができません。

### 今回の問題点​

システムが**ある年月日当時の消税率**を元に金額の計算を多用するようなものだとこの暗黙の税率変更は問題になります。過去の金額もすべて現在の消費税率である10%で計算されてしまうからです。

### named exportだと​

named exportであれば`export`する名称を変更することで呼び出し側の変更を強制させることができます。

```
taxIncluded.tsts`export  const  <data-lsp lsp="const taxIncludedAsOf2014: (price: any) => number">taxIncludedAsOf2014</data-lsp>  = (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.08;`
```

```
taxIncluded.tsts`export  const <data-lsp lsp="const taxIncludedAsOf2014: (price: any) => number">taxIncludedAsOf2014</data-lsp> = (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.08;`
```

```
index.tsts`import { <data-lsp lsp="(alias) const taxIncludedAsOf2014: (i: number) => number
import taxIncludedAsOf2014">taxIncludedAsOf2014</data-lsp> } from  "./taxIncluded";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncludedAsOf2014(i: number): number
import taxIncludedAsOf2014">taxIncludedAsOf2014</data-lsp>(100));108`
```

```
index.tsts`import { <data-lsp lsp="(alias) const taxIncludedAsOf2014: (i: number) => number
import taxIncludedAsOf2014">taxIncludedAsOf2014</data-lsp> } from  "./taxIncluded";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncludedAsOf2014(i: number): number
import taxIncludedAsOf2014">taxIncludedAsOf2014</data-lsp>(100));108`
```

税率が10%に変われば次のようにします。

```
taxIncluded.tsts`export  const  <data-lsp lsp="const taxIncludedAsOf2019: (price: any) => number">taxIncludedAsOf2019</data-lsp>  = (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.1;`
```

```
taxIncluded.tsts`export  const <data-lsp lsp="const taxIncludedAsOf2019: (price: any) => number">taxIncludedAsOf2019</data-lsp> = (<data-lsp lsp="(parameter) price: any">price</data-lsp>) => <data-lsp lsp="(parameter) price: any">price</data-lsp> *  1.1;`
```

```
index.tsts`import { <data-lsp lsp="(alias) const taxIncludedAsOf2019: (i: number) => number
import taxIncludedAsOf2019">taxIncludedAsOf2019</data-lsp> } from  "./taxIncluded";// this is no longer available.// console.log(taxIncludedAsOf2014(100));<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncludedAsOf2019(i: number): number
import taxIncludedAsOf2019">taxIncludedAsOf2019</data-lsp>(100));110`
```

```
index.tsts`import { <data-lsp lsp="(alias) const taxIncludedAsOf2019: (i: number) => number
import taxIncludedAsOf2019">taxIncludedAsOf2019</data-lsp> } from  "./taxIncluded";// this is no longer available.// console.log(taxIncludedAsOf2014(100));<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) taxIncludedAsOf2019(i: number): number
import taxIncludedAsOf2019">taxIncludedAsOf2019</data-lsp>(100));110`
```

名前を変更したため、呼び出し元も名前の変更が強制されます。これはたとえ`as`を使って名前を変更していたとしても同じく変更する必要があります。

ロジックが変わったこととそれによる修正を強制したいのであればnamed exportを使う方がわかりやすく、そしてエディター、IDEを通して見つけやすくなる利点があります。逆に、公開するパッケージのようにAPIが一貫して明瞭ならばdefault exportも価値があります。
