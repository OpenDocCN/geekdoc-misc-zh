# 🚧モジュール

> 原文：[`typescriptbook.jp/reference/modules`](https://typescriptbook.jp/reference/modules)

注意

**Experimental!** このページは執筆途中の草稿です。構成が大きく変わることがありえますので、リンクなどをする場合はリンク切れが起こる可能性がある点をご留意ください。このページの内容は、import���export、requireをもとに再構成・加筆しています。

## モジュールの基礎​

### モジュールの目的​

プログラムは大きさがさまざまです。行数で見ると、数行のものから数万行のものまであります。

小さいプログラムなら、1つのファイルでも十分ですが、大きなプログラムは1つのファイルだけで作るのは大変です。

想像してみてください。何千行もあるプログラムが1つのファイルに詰め込まれている状態は、読みにくく、修正もしにくくなります。

1.  **保守性の問題** ─ 保守性が低いことです。大量のコードが1つのファイルに詰め込まれているため、変更がしにくいです。コードの見通しが悪いため、1 行の変更が他の数千行にどのような影響を与えるのか、予想もつかないことがあります。これは、変更に対して臆病になってしまう原因にもなります。

1.  **変数名の衝突** ─ コードが長いと、変数名が衝突する危険性が高まります。これにより、関係のない変数を上書きしてしまう恐れがあります。これを避けるために変数名を長くすることもありますが、それは可読性を損ねる原因になります。

1.  **再利用の問題** ─ たとえば、数千行のコードの中から特定の部分だけを別のプロジェクトで使用したい場合、それらが1つの大きな塊にまとめられているため、必要な部分だけを抜き出せません。無理に読み込むと、不要なコードも一緒に読み込んでしまい、それがどう悪さをするかは予想がつきません。

このような問題を解決するのが、**モジュール**(module)と呼ばれる仕組みです。モジュールは1つのファイルを複数のファイルに分割し、関連付けて、ひとつのプログラムとして動かすことができます。

大規模なプログラムを作る場合、それぞれの機能ごとにモジュールを分けることで、各モジュールを読みやすく、保守性も高く、再利用もしやすくなります。

### JavaScriptのモジュール​

JavaScriptのモジュールは、`export`または`import`を1つ以上含むJavaScriptファイルを言います。

+   `export`は他のモジュールに変数を公開するためのキーワードです。

+   `import`は他のモジュールから変数をインポートするキーワードです。

`export`と`import`を使うと、モジュール間で変数を受け渡しできるようになります。

たとえば、次は変数`world`をエクスポートしているモジュールです。

```
world.jsts`export  const  <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>  =  "World";`
```

```
world.jsts`export  const  <data-lsp lsp="const world: &quot;World&quot;">world</data-lsp>  =  "World";`
```

別のファイルでこれをインポートして使います。

```
hello.jsts`import { <data-lsp lsp="(alias) const world: &quot;World&quot;
import world">world</data-lsp> } from  "./world";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Hello ${<data-lsp lsp="(alias) const world: &quot;World&quot;
import world">world</data-lsp>}`);Hello World`
```

```
hello.jsts`import { <data-lsp lsp="(alias) const world: &quot;World&quot;
import world">world</data-lsp> } from  "./world";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Hello ${<data-lsp lsp="(alias) const world: &quot;World&quot;
import world">world</data-lsp>}`);Hello World`
```

### 値の公開と非公開​

JavaScriptのモジュールは、明示的に`export`をつけた値だけが公開され、他のモジュールから参照できます。たとえば、次の例の`publicValue`は他のモジュールから利用できます。一方、`privateValue`は外部からは利用できません。

```
js`export  const  <data-lsp lsp="const publicValue: 1">publicValue</data-lsp>  =  1;const  <data-lsp lsp="const privateValue: 2">privateValue</data-lsp>  =  2;`
```

```
js`export  const  <data-lsp lsp="const publicValue: 1">publicValue</data-lsp>  =  1;const  <data-lsp lsp="const privateValue: 2">privateValue</data-lsp>  =  2;`
```

JavaScriptのモジュールでは、デフォルトで変数や関数などは非公開になるわけです。Javaなどの他の言語では、モジュール(パッケージ)のメンバーがデフォルトで公開になり、非公開にしたいものには`private`修飾子をつける言語があります。そういった言語と比べると、JavaScriptは基本方針が真逆なので注意が必要です。

### パッケージとモジュールの違い​

モジュールと似た用語に、パッケージ(package)という言葉があります。プログラミング言語によって、モジュールとパッケージの定義は異なります。JavaScriptでは、これらはどのように捉えられているでしょうか。

モジュールは、基本的にひとつひとつのJavaScript/TypeScriptファイルを指します。詳細は「[スクリプトとモジュール](https://typescriptbook.jp/reference/import-export-require#%E3%82%B9%E3%82%AF%E3%83%AA%E3%83%97%E3%83%88%E3%81%A8%E3%83%A2%E3%82%B8%E3%83%A5%E3%83%BC%E3%83%AB)」のセクションで説明しますが、JavaScript/TypeScriptファイルのうち、`export`または`import`を1つ以上含んだものがモジュールに当たります。

パッケージは、package.jsonとJavaScriptファイル群を持つディレクトリを指します。package.jsonは、パッケージの名前、バージョン、ライセンスなどのメタデータを記載したファイルです。

モジュールとパッケージには、利用用途の違いがあります。一般的なアプリケーション開発では、複数のJavaScript/TypeScriptファイルに分けて開発します。この際に作られるファイルひとつひとつがモジュールになります。アプリケーションの保守性の担保、コードの再利用性の確保、変数名衝突の回避のために用いられるのがモジュールです。

一方、パッケージの典型的な目的は配布です。ライブラリ製作者が、プログラムを他者に配布する際に用いられるのがパッケージです。そして、アプリケーション開発者は、自己のアプリケーションにパッケージを組み込む形で、パッケージは利用されていきます。

## モジュールとエコシステム​

### バンドラー​

JavaScriptでは、複数のJavaScriptファイルを1つのファイルに繋ぎ合わせることをバンドル(bundle)と言います。バンドルを、自動的に行なう開発ツールを、バンドラー(bundler)と呼びます。バンドラーは「モジュールバンドラー」と呼ばれることもあります。

JavaScriptには、さまざまなバンドラーがあります。たとえば、有名なものとしては次のようなバンドラーがあります。

+   webpack

+   rollup

+   parcel

+   esbuild

+   vite

这些打包工具不仅可以打包 JavaScript，还可以打包 TypeScript、CSS、图像等各种类型的文件。

#### 打包工具的必要性​

如果不使用 JavaScript 打包工具，为了运行 Web 应用程序，需要单独加载多个 JavaScript 文件。这会带来一些问题。

首先，当 Web 浏览器加载 JavaScript 代码时，会花费很多时间。

其次，由于 JavaScript 文件之间的依赖关系没有整理好，可能会导致代码错误和 bug 的发生。

第三，如果 JavaScript 代码没有经过优化，应用程序的��行性能可能会变差��

解决这些问题的就是打包工具的作用。

#### 在服务器端 JS 中，打包工具的优点并不多​

JavaScript 是为在 Web 浏览器中运行而设计的语言，但也可以在服务器端使用。Node.js 是服务器端 JavaScript 执行环境之一。由于 Node.js 从很早就在内部实现了模块系统，因此即使在 JavaScript 没有 ES 模块这样的模块系统的时代，也可以使用模块。因此，在服务器端 JavaScript 环境中，并不需要打包工具。

最近的 JavaScript 具有模块系统，因此即使不使用打包工具也可以实现模块化。这在前端也是一样的。然而，在前端，下载和执行数百甚至数千个模块会耗费大量时间，因此将它们合并到一个 JavaScript 文件中的打包工具仍然很重要。

另一方面，在服务器端，即使有数百甚至数千个模块，加载模块只发生在服务器启动时。因此，打包工具的优点几乎不存在。

## 模块系统​

### CommonJS 和 ES 模块​

### CommonJS 和 ES 模块混合存在的原因​

在座的各位中，可能有一些人除了 JavaScript 和 TypeScript 之外还有其他编程语言的经验。在其他语言中，您是否使用过同时存在多个模块系统的语言？

JavaScript 至少有两种不同的模块系统，即 ES 模块和 CommonJS。这种情况在编程语言中是罕见的，也是使 JavaScript 模块化变得复杂的因素之一。

那么，为什么 JavaScript 会有两种模块系统呢？在这里，我们将从历史上的发展来解释 JavaScript 目前的状况。

#### 第一个模块系统​

JavaScript 的模块系统在服务器端 JavaScript，尤其是 Node.js 的背景下，比在浏览器端更早得到发展。

CommonJS 是 JavaScript 中广泛使用的模块系统之一。追溯 CommonJS 的历史，可以追溯到 2009 年的 ServerJS 成立。ServerJS 旨在使 JavaScript 在服务器端可用，并制定了服务器端 JavaScript 的通用 API 的标准化项目。后来，更名为 CommonJS。

将 JavaScript 引入服务器端并不是一帆风顺，直接将浏览器的 JavaScript 引入服务器端并不奏效。例如，浏览器有`<script>`标签，因此可以通过在页面上写入多个`<script>`标签来执行多个 JavaScript。但是，在服务器端没有页面的概念。

此外，当时的 JavaScript 也没有像 ES 模块这样的模块系统。因此，必须从考虑如何加载多个 JavaScript 文件开始。

于是，CommonJS 模块规范应运而生。大家熟悉的`require()`和`module.exports`。CommonJS 通过在 JavaScript 当时不存在模块系统的语法和功能框架内进行函数和变量的巧妙处理，实现了类似模块的功能。

Node.js 与 CommonJS 同时发布，但 Node.js 采用的模块系统是 CommonJS。这使得在 Node.js 中，即使在服务器端 JavaScript 中也可以分割文件并加载多个文件。这种模块系统开始受到 Node.js 用户的欢迎，npm 等库的发布，模块生态系统也得到了发展。

顺便说一句，就在 CommonJS 和 Node.js 开始的 2009 年前一年，发生了 ECMAScript 4 草案的废弃事件。ES4 中包含了向 JavaScript 添加模块系统的规范。如果 ES4 实现了，CommonJS 可能就不再需要了。然而，实际情况是，由于制定 ES 规范的浏览器供应商之间存在分歧和冲突，改进 JavaScript 的努力以争吵告终。

由于 Node.js 的推出时间不太合适，JavaScript 本身很难改进模块系统。因此，可以将 Node.js 视为现有 JavaScript 范围内的解决方案，采用 CommonJS 作为模块系统。

CommonJS 起源于服务器端，并得到发展。也产生了许多基于 CommonJS 的库。这些库在客户端也有需求。因此，从 webpack 开始，模块打包工具开始支持 CommonJS。虽然 CommonJS 起源于服务器端，但随着模块打包工具的支持，前端也开始依赖 CommonJS。

#### 另一种模块系统​

从 CommonJS 的诞生到现在，历史在流逝，到了 2015 年，确定了新的 JavaScript 标准规范 ES6。这是 JavaScript 10 年来的一次重大更新。其中包括实现名为 ES6 Modules 的模块系统的规范。大家熟知的 `import` 和 `export` 就是其中的一部分。这是 JavaScript 的第一个原生模块系统。如果说 CommonJS 是通过基层活动规范化的模块系统，那么 ES 模块可以说是官方发布的标准模块系统。

JavaScript 领域，在支持 ES6 的同时，无论是服务器端还是客户端，在 2016 年左右开始讨论引入 ES 模块。讨论的重点仍然是传统模块系统 CommonJS 和新系统 ES 模块的共存。

当 ES 模块规范确定下来时，JavaScript 已经建立了一个基于 CommonJS 的环境，并且由于有很多符合 CommonJS 标准的 NPM 包，所以没有放弃 CommonJS 的选择。如果放弃了 CommonJS，那么几乎所有过去的资产都将丢失，因此 CommonJS 和 ES 模块的共存对于 Node.js 来说是一个重要的主题。

例如，即使在服务器端 JavaScript 的 Node.js 中，经过长时间的讨论，ES 模块在 2017 年的 Node.js v8.5.0 中作为实验性功能发布。随后，在 2019 年的 v13.2.0 中，ES 模块从“实验性功能”中移除标签，升级为预期用于生产的功能。然后在 2020 年，CommonJS 的命名导出可以通过 ES 模块的命名导入进行加载，逐渐使 Node.js 中的 ES 模块环境完善。

尽管 ES 模块环境已经完善，但 CommonJS 已经支持 JavaScript 超过 10 年，已经成为不可分割的关系。因此，目前，JavaScript 中存在着两种模块系统。

#### 总结​

+   JavaScript 有 CommonJS 和 ES 模块两种模块系统。

+   CommonJS 与 JavaScript 有着超过 10 年的深厚联系。

+   JavaScript 领域选择了 CommonJS 和 ES 模块共存的道路。

### CommonJS 和 ES 模块的区别​

#### `import` 和 `require` 的区别​

在 JavaScript 中，当从模块中导入变量等值时，使用 `import` 和 `require`。这两者非常相似，但它们分别是不同的模块系统的写法。

JavaScript 的模块系统有几种，但其中两种代表性的是：

+   ES 模块

+   CommonJS

有关这两种模块系统的详细区别，请参考**(TODO 参考文章)**。

##### import​

`import` 是用于 ES 模块的 JavaScript 模块系统的语法。`import` 用于导入其他模块中导出的变量或函数。例如，可以这样使用。

```
js`import { myVariable, myFunction } from  "./myModule";`
```

```
js`import { myVariable, myFunction } from  "./myModule";`
```

##### require​

另一方面，`require` 是用于 CommonJS 这种模块系统的函数。`require` 函数用于从其他模块导入变量或函数。例如，可以这样使用。

```
js`const { myVariable,  myFunction } =  require("./myModule");`
```

```
js`const { myVariable,  myFunction } = require("./myModule");`
```

#### `export` 和 `module.exports` 的区别​

`import` 和 `require` 用于从其他模块导入值。作为对应，还有 `export` 和 `module.export` 用于将值导出到其他模块。`export` 和 `module.export` 也分别用于不同的模块系统。

##### export​

JavaScript 的 `export` 是用于 ES 模块这种模块系统的语法。使用 `export` 可以将模块内定义的变量或函数等导出。例如，可以这样使用。

```
js`export  const  myVariable  =  "foo";export  const  myFunction  = () => {  /* 関数の処理 */};`
```

```
js`export  const  myVariable  =  "foo";export  const myFunction = () => {  /* 関数の処理 */};`
```

##### module.exports​

另一方面，`module.exports` 是用于 CommonJS 这种模块系统的变量。在 CommonJS 中，通过将模块内定义的变量或函数赋值给 `module.exports`，可以导出它们。例如，可以这样写。

```
js`module.exports.myVariable =  "foo";module.exports.myFunction  = () => {  /* 関数の処理 */};`
```

```
js`module.exports.myVariable =  "foo";module.exports.myFunction = () => {  /* 関数の処理 */};`
```

## ES 模块的语法​

## 模块解析​

## ES 模块规范​

## CommonJS 的 API​

## TypeScript 和模块​

## ES 模块的最佳实践​
