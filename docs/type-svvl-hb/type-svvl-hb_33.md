# 类型定义文件 (.d.ts)

> 原文：[`typescriptbook.jp/reference/declaration-file`](https://typescriptbook.jp/reference/declaration-file)

在自己的项目中使用 TypeScript 编码时，通过声明类型可以使用 IDE 或编辑器的自动补全功能和代码检查。但是在使用外部包（npm）时，并不一定包含类型定义文件。

## 什么是类型定义文件​

类型定义文件是包含可访问声明的文件。其扩展名为`.d.ts`。

类型定义文件主要用于分发包。当 TypeScript 编译为 JavaScript 时，类型信息会丢失。直接使用 JavaScript 包时无法享受类型定义的好处。但通过包含类型定义文件，可以作为补充和代码检查使用。

遗憾的是，并非所有发布在 npm 上的包都一定有类型定义文件。关于此问题，将在**类型定义文件的有无**中进行说明。

### 类型定义文件示例​

使用`tsc`命令并带上`-d`选项进行编译，即可输出 JavaScript 和类型定义文件。

#### TypeScript 文件​

尝试使用带有`-d`选项的`tsc`命令编译下面的 TypeScript 文件（sample.ts）。

```
sample.tsts`interface  <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}function  <data-lsp lsp="function greeter(person: Person): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: Person">person</data-lsp>:  <data-lsp lsp="interface Person">Person</data-lsp>):  string {  return  "Hello, "  +  <data-lsp lsp="(parameter) person: Person">person</data-lsp>.<data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp> +  " "  +  <data-lsp lsp="(parameter) person: Person">person</data-lsp>.<data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>;}`
```

```
sample.tsts`interface <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}function <data-lsp lsp="function greeter(person: Person): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: Person">person</data-lsp>: <data-lsp lsp="interface Person">Person</data-lsp>):  string {  return  "Hello, "  +  <data-lsp lsp="(parameter) person: Person">person</data-lsp>.<data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp> +  " "  +  <data-lsp lsp="(parameter) person: Person">person</data-lsp>.<data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>;}`
```

使用`tsc`命令并带上`-d`选项进行编译。

```
bash`tsc -d`
```

```
bash`tsc -d`
```

#### JavaScript 文件​

在`sample.ts`中使用了接口，但由于 JavaScript 中没有接口的概念，因此仅限于函数。同时，参数的类型信息也会丢失。

```
sample.jsjs`function  <data-lsp lsp="function greeter(person: any): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: any">person</data-lsp>) {  return  "Hello, "  +  <data-lsp lsp="(parameter) person: any">person</data-lsp>.<data-lsp lsp="any">firstName</data-lsp> +  " "  +  <data-lsp lsp="(parameter) person: any">person</data-lsp>.<data-lsp lsp="any">lastName</data-lsp>;}//# sourceMappingURL=sample.js.map`
```

```
sample.jsjs`function <data-lsp lsp="function greeter(person: any): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: any">person</data-lsp>) {  return  "Hello, "  +  <data-lsp lsp="(parameter) person: any">person</data-lsp>.<data-lsp lsp="any">firstName</data-lsp> +  " "  +  <data-lsp lsp="(parameter) person: any">person</data-lsp>.<data-lsp lsp="any">lastName</data-lsp>;}//# sourceMappingURL=sample.js.map`
```

#### `d.ts`文件​

仅包含定义信息的文件将被输出。

```
sample.d.tsts`interface  <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}declare  function  <data-lsp lsp="function greeter(person: Person): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: Person">person</data-lsp>:  <data-lsp lsp="interface Person">Person</data-lsp>):  string;`
```

```
sample.d.tsts`interface <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}declare  function <data-lsp lsp="function greeter(person: Person): string">greeter</data-lsp>(<data-lsp lsp="(parameter) person: Person">person</data-lsp>: <data-lsp lsp="interface Person">Person</data-lsp>):  string;`
```

## 类型定义文件的有无​

类型定义文件由包开发者或志愿者创建。

+   有类型定义文件

    +   使用 TypeScript 编写的包

    +   JavaScript 编写的包，但包含`.d.ts`文件

+   有类型定义文件但需要单独安装

    +   JavaScript 编写的包，但已在 DefinitelyTyped 中注册

+   无类型定义文件

    +   JavaScript 编写的包中不存在类型定义文件

### 有类型定义文件​

当查看 NPM 包的介绍页面时，如果包名称右侧显示有 TS 图标，则表示存在类型定义文件。

这表示包开发者正在使用 TypeScript 开发，或者使用 JavaScript 开发但包含了类型定义文件。对于包含类型定义文件的包，无需特殊操作。

例如，日期库[date-fns](https://date-fns.org/)是用 JavaScript 构建的，但附带了`typings.d.ts`。只需安装即可享受定义文件的好处。

```
bash`npm install date-fns`
```

```
bash`npm install date-fns`
```

如果存在类型定义文件，则无需额外配置即可引用类型信息。

### 有类型定义文件但需要单独安装​

当查看 NPM 包��介绍页面时，如果包名称右侧显示有 DT 图标，则表示该包本身不包含类型定义文件，但已在[DefinitelyTyped](https://github.com/DefinitelyTyped/DefinitelyTyped)中注册。

在这种情况下，您需要在安装包后单独安装类型定义文件。安装定义文件也使用`npm`命令。

例如，[Express](https://expressjs.com/)是用 JavaScript 构建的，但类型定义文件需要单独安装`@types/express`包。

[Express](https://expressjs.com/)的安装示例如下。

```
bash`npm install express --save # express 本体のインストールnpm install @types/express --save-dev # 型定義ファイルのインストール`
```

```
bash`npm install express --save # express 本体のインストールnpm install @types/express --save-dev # 型定義ファイルのインストール`
```

### 无类型定义文件​

也存在没有类型定义文件的库。在这种情况下

1.  通过`any`进行妥协

1.  创建类型定义文件

即使没有类型定义文件，也可以使用不明确的`any`类型。同时，您也可以自行创建并发布到 DefinitelyTyped。

[贡献方法 | Definitely Typed](https://github.com/DefinitelyTyped/DefinitelyTyped/blob/master/README.ja.md#%E3%82%B3%E3%83%B3%E3%83%88%E3%83%AA%E3%83%93%E3%83%A5%E3%83%BC%E3%83%88%E8%B2%A2%E7%8C%AE%E3%81%99%E3%82%8B%E6%96%B9%E6%B3%95)

## 型定义文件中出现的关键字​

为了能够阅读类型定义文件，我们将介绍在类型定义文件中常用的关键字。

### 声明​

使用`declare`关键字可以告诉 TypeScript 变量、函数、类等在 JavaScript 中“存在”。这被称为“环境声明”。

假设下面的文件作为 JavaScript 库被加载，并且全局函数`hello`可用。

```
js`function  <data-lsp lsp="function hello(name: any): string">hello</data-lsp>(<data-lsp lsp="(parameter) name: any">name</data-lsp>) {  return  "Hello, "  + <data-lsp lsp="(parameter) name: any">name</data-lsp>;}`
```

```
js`function <data-lsp lsp="function hello(name: any): string">hello</data-lsp>(<data-lsp lsp="(parameter) name: any">name</data-lsp>) {  return  "Hello, "  + <data-lsp lsp="(parameter) name: any">name</data-lsp>;}`
```

この状態でTypeScriptで`hello`関数を呼び出すと型エラーが発生します。これは、TypeScriptが`hello`関数が存在することを知らないためです。

```
ts`<data-err><data-lsp lsp="any">hello</data-lsp></data-err>("taro");Cannot find name 'hello'.2304Cannot find name 'hello'.`
```

```
ts`<data-err><data-lsp lsp="any">hello</data-lsp>(</data-err>"taro");Cannot find name 'hello'.2304Cannot find name 'hello'.`
```

`declare`を利用してアンビエント宣言をすることで、TypeScriptにJavaScript 内のどこかに`hello`関数が「存在する」ことを宣言することができます。これによりTypeScriptが`hello`関数を認識できるようになります。

```
ts`declare  function  <data-lsp lsp="function hello(name: string): string">hello</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string;<data-lsp lsp="function hello(name: string): string">hello</data-lsp>("taro");"hello, taro"`
```

```
ts`declare  function <data-lsp lsp="function hello(name: string): string">hello</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string;<data-lsp lsp="function hello(name: string): string">hello</data-lsp>("taro");"hello, taro"`
```

実際のモジュールの型定義ファイルの例として`jest`の型定義ファイルを見てみましょう。`beforeAll`などの関数が型定義ファイル内でアンビエント宣言されているのが確認できます。これによりモジュールの読み込みをしなくても、TypeScriptが`beforeAll`を関数として認識することができます。

```
node_modules/@types/jest/index.d.tsts`declare  var <data-lsp lsp="var beforeAll: jest.Lifecycle">beforeAll</data-lsp>:  <data-lsp lsp="namespace jest">jest</data-lsp>.<data-lsp lsp="type jest.Lifecycle = (fn: ProvidesHookCallback, timeout?: number) => any">Lifecycle</data-lsp>;declare  namespace  <data-lsp lsp="namespace jest">jest</data-lsp> {  type  <data-lsp lsp="type jest.Lifecycle = (fn: ProvidesHookCallback, timeout?: number) => any">Lifecycle</data-lsp>  = (<data-lsp lsp="(parameter) fn: ProvidesHookCallback">fn</data-lsp>:  <data-lsp lsp="type ProvidesHookCallback = /*unresolved*/ any">ProvidesHookCallback</data-lsp>, <data-lsp lsp="(parameter) timeout: number | undefined">timeout</data-lsp>?:  number) =>  any;}`
```

```
node_modules/@types/jest/index.d.tsts`declare  var <data-lsp lsp="var beforeAll: jest.Lifecycle">beforeAll</data-lsp>: <data-lsp lsp="namespace jest">jest</data-lsp>.<data-lsp lsp="type jest.Lifecycle = (fn: ProvidesHookCallback, timeout?: number) => any">Lifecycle</data-lsp>;declare  namespace <data-lsp lsp="namespace jest">jest</data-lsp> {  type <data-lsp lsp="type jest.Lifecycle = (fn: ProvidesHookCallback, timeout?: number) => any">Lifecycle</data-lsp> = (<data-lsp lsp="(parameter) fn: ProvidesHookCallback">fn</data-lsp>: <data-lsp lsp="type ProvidesHookCallback = /*unresolved*/ any">ProvidesHookCallback</data-lsp>, <data-lsp lsp="(parameter) timeout: number | undefined">timeout</data-lsp>?:  number) =>  any;}`
```

### namespace​

`namespace`キーワードを使うことで名前空間を定義することができます。

名前空間を定義することで、型名の衝突を避けることができます。

`Element`という型をライブラリの型として定義してライブラリ利用者が参照できるようにしたいと考えみます。この型はTypeScriptの`lib.dom.d.ts`にすでに定義されているため、そのまま同じグローバルな空間に定義をすると名前が衝突してしまいます。

```
node_modules/typescript/lib/lib.dom.d.tsts`interface  <data-lsp lsp="interface Element">Element</data-lsp>  extends  <data-lsp lsp="interface Node">Node</data-lsp>,  <data-lsp lsp="interface ARIAMixin">ARIAMixin</data-lsp>,  <data-lsp lsp="interface Animatable">Animatable</data-lsp>,  <data-lsp lsp="interface ChildNode">ChildNode</data-lsp>,  <data-lsp lsp="interface InnerHTML">InnerHTML</data-lsp>,  <data-lsp lsp="interface NonDocumentTypeChildNode">NonDocumentTypeChildNode</data-lsp>,  <data-lsp lsp="interface ParentNode">ParentNode</data-lsp>,  <data-lsp lsp="interface Slottable">Slottable</data-lsp> {  readonly <data-lsp lsp="(property) Element.attributes: NamedNodeMap">attributes</data-lsp>:  <data-lsp lsp="interface NamedNodeMap">NamedNodeMap</data-lsp>;  /** Allows for manipulation of element's class content attribute as a set of whitespace-separated tokens through a DOMTokenList object. */  readonly <data-lsp lsp="(property) Element.classList: DOMTokenList">classList</data-lsp>:  <data-lsp lsp="interface DOMTokenList">DOMTokenList</data-lsp>;  // 省略}`
```

```
node_modules/typescript/lib/lib.dom.d.tsts`interface <data-lsp lsp="interface Element">Element</data-lsp>  extends <data-lsp lsp="interface Node">Node</data-lsp>, <data-lsp lsp="interface ARIAMixin">ARIAMixin</data-lsp>, <data-lsp lsp="interface Animatable">Animatable</data-lsp>, <data-lsp lsp="interface ChildNode">ChildNode</data-lsp>, <data-lsp lsp="interface InnerHTML">InnerHTML</data-lsp>, <data-lsp lsp="interface NonDocumentTypeChildNode">NonDocumentTypeChildNode</data-lsp>, <data-lsp lsp="interface ParentNode">ParentNode</data-lsp>, <data-lsp lsp="interface Slottable">Slottable</data-lsp> {  readonly <data-lsp lsp="(property) Element.attributes: NamedNodeMap">attributes</data-lsp>: <data-lsp lsp="interface NamedNodeMap">NamedNodeMap</data-lsp>;  /** Allows for manipulation of element's class content attribute as a set of whitespace-separated tokens through a DOMTokenList object. */  readonly <data-lsp lsp="(property) Element.classList: DOMTokenList">classList</data-lsp>: <data-lsp lsp="interface DOMTokenList">DOMTokenList</data-lsp>;  // 省略}`
```

次のコードは`namespace`を使わずにライブラリ独自の型として`Element`を定義している例です。TypeScriptでは同じインターフェースが定義された場合は宣言のマージが発生するため、`lib.dom.d.ts`で定義されている型とマージされるため、`attributes`プロパティなど複数プロパティの指定を求められてしまいます。

```
ts`// hello.d.tsinterface  <data-lsp lsp="interface Element">Element</data-lsp> { <data-lsp lsp="(property) Element.id: string">id</data-lsp>:  string;}// index.tsconst  <data-err><data-lsp lsp="const e: Element">e</data-lsp></data-err>:  <data-lsp lsp="interface Element">Element</data-lsp>  = {Type '{ id: string; }' is missing the following properties from type 'Element': attributes, classList, className, clientHeight, and 163 more.2740Type '{ id: string; }' is missing the following properties from type 'Element': attributes, classList, className, clientHeight, and 163 more. <data-lsp lsp="(property) Element.id: string">id</data-lsp>:  "1",};`
```

```
ts`// hello.d.tsinterface <data-lsp lsp="interface Element">Element</data-lsp> { <data-lsp lsp="(property) Element.id: string">id</data-lsp>:  string;}// index.tsconst  <data-err><data-lsp lsp="const e: Element">e</data-lsp></data-err>: <data-lsp lsp="interface Element">Element</data-lsp> = {Type '{ id: string; }' is missing the following properties from type 'Element': attributes, classList, className, clientHeight, and 163 more.2740Type '{ id: string; }' is missing the following properties from type 'Element': attributes, classList, className, clientHeight, and 163 more. <data-lsp lsp="(property) Element.id: string">id</data-lsp>:  "1",};`
```

名前空間を定義することで衝突を避けてライブラリ独自の型を定義をすることができます。

```
ts`// @filename: hello.d.tsnamespace  <data-lsp lsp="namespace Hello">Hello</data-lsp> {  interface  <data-lsp lsp="interface Hello.Element">Element</data-lsp> { <data-lsp lsp="(property) Hello.Element.id: number">id</data-lsp>:  number; }}// @filename: index.tsconst  <data-lsp lsp="const e: Hello.Element">e</data-lsp>:  <data-lsp lsp="namespace Hello">Hello</data-lsp>.<data-lsp lsp="interface Hello.Element">Element</data-lsp>  = { <data-lsp lsp="(property) Hello.Element.id: number">id</data-lsp>:  1,};`
```

```
ts`// @filename: hello.d.tsnamespace <data-lsp lsp="namespace Hello">Hello</data-lsp> {  interface <data-lsp lsp="interface Hello.Element">Element</data-lsp> { <data-lsp lsp="(property) Hello.Element.id: number">id</data-lsp>:  number; }}// @filename: index.tsconst  <data-lsp lsp="const e: Hello.Element">e</data-lsp>: <data-lsp lsp="namespace Hello">Hello</data-lsp>.<data-lsp lsp="interface Hello.Element">Element</data-lsp> = { <data-lsp lsp="(property) Hello.Element.id: number">id</data-lsp>:  1,};`
```

Reactの型定義ファイルでは、次のように`namespace JSX`で名前空間が定義されて`Element`の型が定義がされています。

`declare global` と `declare namespace`の違いについて

型定義ファイルでは同じ振る舞いをするため違いはない。`declare global`と記述をすることで、グローバルスコープに名前空間を定義するということを開発者の意図として明示できる？

```
ts`// @filename: node_modules/@types/react/index.d.tsdeclare <data-lsp lsp="namespace global">global</data-lsp> {  namespace  <data-lsp lsp="namespace global.JSX">JSX</data-lsp> {  interface  <data-lsp lsp="interface global.JSX.Element">Element</data-lsp>  extends  <data-lsp lsp="any">React</data-lsp>.<data-lsp lsp="any">ReactElement</data-lsp><any,  any> {}  // 省略 }}`
```

```
ts`// @filename: node_modules/@types/react/index.d.tsdeclare <data-lsp lsp="namespace global">global</data-lsp> {  namespace <data-lsp lsp="namespace global.JSX">JSX</data-lsp> {  interface <data-lsp lsp="interface global.JSX.Element">Element</data-lsp> extends <data-lsp lsp="any">React</data-lsp>.<data-lsp lsp="any">ReactElement</data-lsp><any,  any> {}  // 省略 }}`
```

### module​

TypeScript1.5 以前では、`module`キーワードが「内部モジュール（名前空間）」を定義するために使用されていました。これは現在の`namespace`の機能と同等です。しかし、この名前がESModuleの「外部モジュール」の定義とキーワード名が重複し、混乱を招いてしまう可能性があったため、TypeScript1.5から「内部モジュール」は「名前空間」と呼ばれるように変更され、`namespace`キーワードが新たに導入されました。

現在では、`module`キーワードは非推奨となっているため、`namespace`キーワードの使用をするようにしてください。

### トリプルスラッシュ・ディレクティブ​

型定義ファイルの先頭で見かける3つのスラッシュ(`///`)ではじめるコメント行をトリプルスラッシュ・ディレクティブと呼びます。これは、TypeScript 独自の形式でコンパイラに対して指示を出す機能を持っています。

トリプルスラッシュ・ディレクティブにはいくつかの種類が存在しており、ここでは多くの型定義ファイルで目にする代表的なディレクティブを2つ紹介します。

#### `/// <reference path="..." />` (参照ディレクティブ)​

参照ディレクティブはコンパイラに型定義ファイル間の依存関係を宣言でき、`path`で指定された型定義ファイルを追加でコンパイル時に読み込むように指示を与えることができます。たとえば、次の例では`index.d.ts`をコンパイラが読み込む際に追加で`global.d.ts`を読み込みます。

```
node_modules/@types/react/index.d.tsts`/// <reference  path="global.d.ts" />`
```

```
node_modules/@types/react/index.d.tsts`/// <reference  path="global.d.ts" />`
```

#### `/// <reference types="..." />` (型ディレクティブ)​

型ディレクティブはnpmパッケージへの依存関係を宣言できます。宣言されたパッケージの依存を解決する処理はimport 文でのパッケージの解決と似た処理のため、型ディレクティブは型のimportのようなものとも考えられます。

次の例はexpressの型定義ファイルの一部です。型ディレクティブで`serve-static`パッケージの型定義ファイルに依存していることが示されています。

```
node_modules/@types/express/index.d.tsts`/// <reference  types="express-serve-static-core" />/// <reference  types="serve-static" />`
```

```
node_modules/@types/express/index.d.tsts`/// <reference  types="express-serve-static-core" />/// <reference  types="serve-static" />`
```
