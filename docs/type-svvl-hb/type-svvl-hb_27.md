# JSXとECMAScriptの違い

> 原文：[`typescriptbook.jp/reference/jsx`](https://typescriptbook.jp/reference/jsx)

# JSX

JSX（JavaScript XML）は、コンポーネント指向のJavaScriptライブラリやフレームワーク（特にReact）で一般的に採用されている、JavaScriptの拡張構文です。JSXを用いると、JavaScriptのコード内にHTMLタグのような構文が埋め込み可能となり、より直感的かつ読みやすい形でUIのコードを表現することができます。それによって、開発者のコーディング体験や開発、デバッグの効率が上がります。

JavaScriptの文法はECMAScriptという言語仕様で規定されています。一方、JSXはJavaScriptの構文を独自に拡張した言語です。そのため、JSXはECMAScriptの言語仕様に盛り込まれていません。ブラウザがJavaScriptエンジンを実装する場合は、ECMAScript(標準)に準拠するため、ブラウザで直接 JSXを解釈し、実行することができない現状があります。この問題を解消するためには、JSXをブラウザが認識できるJavaScriptに変換する、いわゆるトランスパイルという過程が必要となります。このトランスパイル作業を助けるツールとして、BabelやTypeScriptコンパイラーが使われます。

## JSX 構文とHTML 構文の違い​

初見では異なると気づきにくいかもしれませんが、実はJSXとHTMLはまったく同じではありません。構文のレベルにおいてJSXとHTMLの間には複数の違いが存在します。一例を挙げると、属性名の表記方法や、スタイルの指定方法、自己終了タグの書き方などが異なります。これらの詳細については後程の「属性」セクションでより詳しく説明します。覚えておくべき重要なポイントとしては、JSXがHTMLとJavaScriptのハイブリッドであるため、両者の規則や慣例を調和させる形で設計されているという点です。

## JSX 構文​

### 要素​

JSXでもっとも一般的な形式は、ネスト可能な要素（タグ）を使ってコンポーネントを表現するものです。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> />;// 描画結果: <br/>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> />;// 描画結果: <br/>`
```

### 入れ子の要素​

JSX 要素はHTMLのようにネストすることができます。たとえば、`div`要素内に2つの`br`要素がネストされている状況を考えてみましょう。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> /> <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> /> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>);// 描画結果: <div><br/><br/></div>`
```

```
tsx`const <data-lsp lsp="const element: React.JSX.Element">element</data-lsp> = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> /> <<data-lsp lsp="(property) JSX.IntrinsicElements.br: React.DetailedHTMLProps<React.HTMLAttributes<HTMLBRElement>, HTMLBRElement>">br</data-lsp> /> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>);// 描画結果: <div><br/><br/></div>`
```

これらは簡単な例ですが、属性や子要素を追加してより複雑なコンポーネントを表現することも可能です。

### テキスト要素​

JSX 内では、要素に直接テキストを書くことができます。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>I'm a text element.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>I'm a text element.</h1>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>I'm a text element.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>I'm a text element.</h1>`
```

上記のように、要素の中に直接テキストを書くと、そのテキストはそのままの形で出力されます。

#### 空白と要素​

JSXでは、要素間のスペースは自動的に無視されます。たとえば、

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>> This is a <<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>>pen</<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>> . </<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>);// 描画結果: <p>This is a<strong>pen</strong>.</p>`
```

```
tsx`const <data-lsp lsp="const element: React.JSX.Element">element</data-lsp> = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>> This is a <<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>>pen</<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>> . </<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>);// 描画結果: <p>This is a<strong>pen</strong>.</p>`
```

上記のコードは「This is a**pen**.」として「a」と「pen」の分かち書きがない状態でレンダリングされてしまいます。

これを回避するには、文字列をJavaScriptの式として書くことです。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>> This is a{" "} <<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>>pen</<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>> . </<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>);// 描画結果: <p>This is a<!-- --> <strong>pen</strong>.</p>`
```

```
tsx`const <data-lsp lsp="const element: React.JSX.Element">element</data-lsp> = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>> This is a{" "} <<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>>pen</<data-lsp lsp="(property) JSX.IntrinsicElements.strong: React.DetailedHTMLProps<React.HTMLAttributes<HTMLElement>, HTMLElement>">strong</data-lsp>> . </<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>);// 描画結果: <p>This is a<!-- --> <strong>pen</strong>.</p>`
```

こうすると、正しく「This is a pen.」としてレンダリングされます。

### 属性​

JSX 属性の名前は、JavaScriptの命名規則に従いcamelCaseで記述することが推奨されています。この命名規則は、HTML 内のアトリビュートとは異なる点に注意が必要です。

### 標準 HTML 属性​

JSXでは、HTML 属性と同じように要素に属性を与えることができます。

```
tsx`const  <data-lsp lsp="const element1: React.JSX.Element">element1</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.img: React.DetailedHTMLProps<React.ImgHTMLAttributes<HTMLImageElement>, HTMLImageElement>">img</data-lsp>  <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.src?: string | undefined">src</data-lsp>="image.jpg"  <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.alt?: string | undefined">alt</data-lsp>="A beautiful scene" />;const  <data-lsp lsp="const element2: React.JSX.Element">element2</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.a: React.DetailedHTMLProps<React.AnchorHTMLAttributes<HTMLAnchorElement>, HTMLAnchorElement>">a</data-lsp>  <data-lsp lsp="(property) React.AnchorHTMLAttributes<HTMLAnchorElement>.href?: string | undefined">href</data-lsp>="http://example.com">Visit our website</<data-lsp lsp="(property) JSX.IntrinsicElements.a: React.DetailedHTMLProps<React.AnchorHTMLAttributes<HTMLAnchorElement>, HTMLAnchorElement>">a</data-lsp>>;`
```

```
tsx`const  <data-lsp lsp="const element1: React.JSX.Element">element1</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.img: React.DetailedHTMLProps<React.ImgHTMLAttributes<HTMLImageElement>, HTMLImageElement>">img</data-lsp> <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.src?: string | undefined">src</data-lsp>="image.jpg" <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.alt?: string | undefined">alt</data-lsp>="A beautiful scene" />;const  <data-lsp lsp="const element2: React.JSX.Element">element2</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.a: React.DetailedHTMLProps<React.AnchorHTMLAttributes<HTMLAnchorElement>, HTMLAnchorElement>">a</data-lsp> <data-lsp lsp="(property) React.AnchorHTMLAttributes<HTMLAnchorElement>.href?: string | undefined">href</data-lsp>="http://example.com">Visit our website</<data-lsp lsp="(property) JSX.IntrinsicElements.a: React.DetailedHTMLProps<React.AnchorHTMLAttributes<HTMLAnchorElement>, HTMLAnchorElement>">a</data-lsp>>;`
```

ただし、`class`属性はJavaScriptの予約語であるため、代わりに`className`を使用します。たとえば、次のコードでは`h1`要素に`className`属性を適用しています。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>  <data-lsp lsp="(property) React.HTMLAttributes<HTMLHeadingElement>.className?: string | undefined">className</data-lsp>="greeting">Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1 class='greeting'>Hello, world!</h1>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp> <data-lsp lsp="(property) React.HTMLAttributes<HTMLHeadingElement>.className?: string | undefined">className</data-lsp>="greeting">Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1 class='greeting'>Hello, world!</h1>`
```

JSXで用いる属性は、JavaScriptのDOMのプロパティ名です。したがって、いくつかのHTML 属性はJSXでは異なる名前を持ちます。次の表は、いくつかの一般的なHTML 属性と対応するJSX 属性名を示しています。

| HTML | JSX |
| --- | --- |
| `class` | `className` |
| `tabindex` | `tabIndex` |
| `for` | `htmlFor` |
| `colspan` | `colSpan` |
| `maxlength` | `maxLength` |
| `cellpadding` | `cellPadding` |
| `cellspacing` | `cellSpacing` |
| `rowspan` | `rowSpan` |

### スタイル属性​

HTMLでは、スタイル属性は一般的に文字列です。

```
html`<div  style="background-color: yellow; color: blue;">Hello!</div>`
```

```
html`<div style="background-color: yellow; color: blue;">Hello!</div>`
```

一方、JSXではスタイル属性はオブジェクトでなければなりません。

```
jsx`<div  style={{ backgroundColor:  "yellow", color:  "blue" }}>Hello!</div>;// 描画結果: <div style='background-color:yellow;color:blue'>Hello!</div>`
```

```
jsx`<div style={{ backgroundColor:  "yellow", color:  "blue" }}>Hello!</div>;// 描画結果: <div style='background-color:yellow;color:blue'>Hello!</div>`
```

### 真偽属性​

真偽属性は要素に特定の特性を指定します。たとえば、input 要素には"disabled"というboolean 型の属性があり、その値に真を指定するとinput 要素は無効になります。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>  <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.disabled?: boolean | undefined">disabled</data-lsp> />;// 描画結果: <input disabled=''/>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.disabled?: boolean | undefined">disabled</data-lsp> />;// 描画結果: <input disabled=''/>`
```

属性の値として`{true}`を付けて明示的に指定することもできます。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>  <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.disabled?: boolean | undefined">disabled</data-lsp>={true} />;// 描画結果: <input disabled=''/>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.disabled?: boolean | undefined">disabled</data-lsp>={true} />;// 描画結果: <input disabled=''/>`
```

しかし、一般的には属性値がtrueの場合、値の部分を省略することが推奨されます。このように記述すると、コードが短くシンプルになるためです。したがって、上記の例のように属性名のみを指定することで、その属性を有効にすることができます。

### 式​

JSX 内ではJavaScriptの式を埋め込むことが可能です。これにより、動的な値をJSX 内に簡単に導入することができます。

### 基本的な式​

JavaScriptの式をJSX 内部に埋め込むためには、波カッコ`{}`を使います。次の例では、変数`name`の値を`<h1>`要素内に埋め込んでいます。

```
tsx`const  <data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>  =  "Josh Perez";const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, {<data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>Hello, <!-- -->Josh Perez</h1>`
```

```
tsx`const  <data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>  =  "Josh Perez";const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, {<data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>Hello, <!-- -->Josh Perez</h1>`
```

ここでは、JavaScriptの変数を埋め込んでいますが、式としての評価結果が挿入されるので、JavaScriptの演算やメソッドの呼び出しも可能です。

```
tsx`const  <data-lsp lsp="const a: 10">a</data-lsp>  =  10;const  <data-lsp lsp="const b: 20">b</data-lsp>  =  20;const  <data-lsp lsp="const sum: React.JSX.Element">sum</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>{<data-lsp lsp="const a: 10">a</data-lsp> + <data-lsp lsp="const b: 20">b</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>30</h1>const  <data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>  =  "Josh Perez";const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, {<data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>.<data-lsp lsp="(method) String.toUpperCase(): string">toUpperCase</data-lsp>()}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>Hello, <!-- -->JOSH PEREZ</h1>`
```

```
tsx`const  <data-lsp lsp="const a: 10">a</data-lsp>  =  10;const  <data-lsp lsp="const b: 20">b</data-lsp>  =  20;const  <data-lsp lsp="const sum: React.JSX.Element">sum</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>{<data-lsp lsp="const a: 10">a</data-lsp> + <data-lsp lsp="const b: 20">b</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>30</h1>const  <data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>  =  "Josh Perez";const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, {<data-lsp lsp="const name: &quot;Josh Perez&quot;">name</data-lsp>.<data-lsp lsp="(method) String.toUpperCase(): string">toUpperCase</data-lsp>()}</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;// 描画結果: <h1>Hello, <!-- -->JOSH PEREZ</h1>`
```

### 条件式​

JavaScriptのif 文は式ではなく文であるため、JSXの式の中に直接書くことはできません。条件式が必要な場合には三項演算子を用います。

```
tsx`const  <data-lsp lsp="const isUser: true">isUser</data-lsp>  =  true;const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <data-lsp lsp="const isUser: true">isUser</data-lsp> ? <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Welcome back!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> : <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Please sign up.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

```
tsx`const  <data-lsp lsp="const isUser: true">isUser</data-lsp>  =  true;const  <data-lsp lsp="const greeting: React.JSX.Element">greeting</data-lsp>  = <data-lsp lsp="const isUser: true">isUser</data-lsp> ? <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Welcome back!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> : <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Please sign up.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

このように、三項演算子`条件式 ? 真の場合の値 : 偽の場合の値`を使うことで、JSX 内で条件によって表示を切り替えることが可能です。

### 短絡評価​

JavaScriptの論理演算子を使用して、短絡評価を行うことも可能です。これを使用すると、特定の条件下でのみ要素を表示したり、デフォルトの値を提供したりします。

### 論理 AND 演算子(`&&`)による短絡評価​

論理 AND 演算子`&&`は、最初の要素が`false`またはfalsyな値（`false`、`null`、`undefined`、`""`、`0`、`NaN`）の場合その値をそのまま返し、それ以外の場合には2 番目の値を返します。

```
tsx`const  <data-lsp lsp="const message: false | React.JSX.Element">message</data-lsp>  = <data-lsp lsp="const isLoggedIn: boolean">isLoggedIn</data-lsp> && <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Welcome back!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

```
tsx`const  <data-lsp lsp="const message: false | React.JSX.Element">message</data-lsp>  = <data-lsp lsp="const isLoggedIn: boolean">isLoggedIn</data-lsp> && <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Welcome back!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

この例では、`isLoggedIn`がtruthyの場合にのみ、`<h1>おかえりなさい！</h1>`が表示されます。

### 論理 OR 演算子(`||`)による短絡評価​

論理 OR 演算子 `||`は、最初のオペランドがtruthyな値の場合にその値をそのまま返し、それ以外の場合には2 番目の値を返します。

```
tsx`const  <data-lsp lsp="const message: true | React.JSX.Element">message</data-lsp>  = <data-lsp lsp="const isLoggedIn: boolean">isLoggedIn</data-lsp> || <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Please sign up.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

```
tsx`const  <data-lsp lsp="const message: true | React.JSX.Element">message</data-lsp>  = <data-lsp lsp="const isLoggedIn: boolean">isLoggedIn</data-lsp> || <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Please sign up.</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

この例では、`isLoggedIn`がfalsyな値（`undefined`、`null`、`""`、`0`、`NaN`）の場合にのみ、`<h1>サインアップしてください。</h1>`が表示されます。

### Null 合体演算子(`??`)���よる短絡評価​

Null 合体演算子(nullish coalescing operator)`??`は、最初のオペランドが`null`または`undefined`の場合にのみ2 番目の値を返します。そのため、最初のオペランドが`false`、`0`、`NaN`、空文字列であっても、その値が保持されます。

```
tsx`const  <data-lsp lsp="const message: string | React.JSX.Element">message</data-lsp>  =  <data-lsp lsp="const input: {
    name?: string | undefined;
}">input</data-lsp>.<data-lsp lsp="(property) name?: string | undefined">name</data-lsp> ?? <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>No input provided.</<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>;`
```

```
tsx`const  <data-lsp lsp="const message: string | React.JSX.Element">message</data-lsp>  =  <data-lsp lsp="const input: {
    name?: string | undefined;
}">input</data-lsp>.<data-lsp lsp="(property) name?: string | undefined">name</data-lsp> ?? <<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>No input provided.</<data-lsp lsp="(property) JSX.IntrinsicElements.p: React.DetailedHTMLProps<React.HTMLAttributes<HTMLParagraphElement>, HTMLParagraphElement>">p</data-lsp>>;`
```

この例では、`input.name`が`null`または`undefined`の場合にのみ、`<p>提供された入力はありません。</p>`が表示されます。

### ループ(反復処理)​ への直接リンク")

JavaScriptの`for-of`ループなど、JSX 内では文を直接使用することができないため、配列の反復処理を行う際は`Array.prototype.map`関数のような式を使用します。式とは、値を返すコードの片段のことで、それに対して文は値を生成しません。JSXは基本的には式ベースのシンタックスですので、式が使われます。

`Array.prototype.map`関数は配列の各要素に対して関数を適用し、その結果で新たな配列を作成します。これを利用して、一連の要素を作ることができます。次にサンプルコードを示します。

```
tsx`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const  <data-lsp lsp="const list: React.JSX.Element">list</data-lsp>  = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.ul: React.DetailedHTMLProps<React.HTMLAttributes<HTMLUListElement>, HTMLUListElement>">ul</data-lsp>> {<data-lsp lsp="const numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.map<React.JSX.Element>(callbackfn: (value: number, index: number, array: number[]) => React.JSX.Element, thisArg?: any): React.JSX.Element[]">map</data-lsp>((<data-lsp lsp="(parameter) number: number">number</data-lsp>) => ( <<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>  <data-lsp lsp="(property) React.Attributes.key?: React.Key | null | undefined">key</data-lsp>={<data-lsp lsp="(parameter) number: number">number</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>()}>{<data-lsp lsp="(parameter) number: number">number</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>> ))} </<data-lsp lsp="(property) JSX.IntrinsicElements.ul: React.DetailedHTMLProps<React.HTMLAttributes<HTMLUListElement>, HTMLUListElement>">ul</data-lsp>>);// 描画結果: <ul><li>1</li><li>2</li><li>3</li></ul>`
```

```
tsx`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const <data-lsp lsp="const list: React.JSX.Element">list</data-lsp> = ( <<data-lsp lsp="(property) JSX.IntrinsicElements.ul: React.DetailedHTMLProps<React.HTMLAttributes<HTMLUListElement>, HTMLUListElement>">ul</data-lsp>> {<data-lsp lsp="const numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.map<React.JSX.Element>(callbackfn: (value: number, index: number, array: number[]) => React.JSX.Element, thisArg?: any): React.JSX.Element[]">map</data-lsp>((<data-lsp lsp="(parameter) number: number">number</data-lsp>) => ( <<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp> <data-lsp lsp="(property) React.Attributes.key?: React.Key | null | undefined">key</data-lsp>={<data-lsp lsp="(parameter) number: number">number</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>()}>{<data-lsp lsp="(parameter) number: number">number</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>> ))} </<data-lsp lsp="(property) JSX.IntrinsicElements.ul: React.DetailedHTMLProps<React.HTMLAttributes<HTMLUListElement>, HTMLUListElement>">ul</data-lsp>>);// 描画結果: <ul><li>1</li><li>2</li><li>3</li></ul>`
```

この例では、`numbers`という配列の各要素に対して関数が適用され、その結果から新たな`<li>`要素で構成された配列が作成されます。そして、その配列は`<ul>`要素に展開され`list`に代入されます。

また、Reactでは配列内の要素に一意な`key`プロパティを追加することが推奨されます。これは、ReactがDOM��変更を効率的に追跡するために使用されます。上記の例では、`key`として数値を文字列に変換したものを使用しています。

### 自己終了タグ​

JSXでは、XMLのように自己終了タグ(self-closing tags)が使用できます。これは、開始タグと終了タグの間に何も内容を持たない要素について使用します。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.img: React.DetailedHTMLProps<React.ImgHTMLAttributes<HTMLImageElement>, HTMLImageElement>">img</data-lsp>  <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.src?: string | undefined">src</data-lsp>="myImage.jpg"  <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.alt?: string | undefined">alt</data-lsp>="" />;`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.img: React.DetailedHTMLProps<React.ImgHTMLAttributes<HTMLImageElement>, HTMLImageElement>">img</data-lsp> <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.src?: string | undefined">src</data-lsp>="myImage.jpg" <data-lsp lsp="(property) React.ImgHTMLAttributes<HTMLImageElement>.alt?: string | undefined">alt</data-lsp>="" />;`
```

その要素が内容を持たない場合でも、`<img></img>`のように書くことは文法的には可能です。しかし、一般的には`<img />`のように自己終了タグを書くことが推奨されます。これは可読性の観点から、タグが内容を持たないことを明示するためです。

### フラグメント​

一般的にJSX 要素は、ひとつの親要素内にすべての子要素をネストしなければなりません。これは、JSXが最終的にひとつのルートノードを返すことを要求するためです。しかし、この要求はしばしばReactのDOM 構造に余計な要素を追加することを強制してしまいます。これを解決するためにReactが提供する機能が「フラグメント」です。

フラグメントを使うと、ひとつの親要素なしに、複数の要素を同時に返すことができます。これにより、無駄なDOMノードの生成を防ぎつつ、構造をくずさずに複数の要素をレンダリングすることができます。

### JSXでのフラグメントの使用​

フラグメントは`<React.Fragment>`タグを使って明示的に表現することができます。次の例では、`h1`と`h2`要素がフラグメント内にまとめられています。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = ( <<data-lsp lsp="(alias) namespace React
import React">React</data-lsp>.<data-lsp lsp="const React.Fragment: React.ExoticComponent<{
    children?: React.ReactNode;
}>">Fragment</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>>Good to see you here.</<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>> </<data-lsp lsp="(alias) namespace React
import React">React</data-lsp>.<data-lsp lsp="const React.Fragment: React.ExoticComponent<{
    children?: React.ReactNode;
}>">Fragment</data-lsp>>);// 描画結果: <h1>Hello!</h1><h2>Good to see you here.</h2>`
```

```
tsx`const <data-lsp lsp="const element: React.JSX.Element">element</data-lsp> = ( <<data-lsp lsp="(alias) namespace React
import React">React</data-lsp>.<data-lsp lsp="const React.Fragment: React.ExoticComponent<{
    children?: React.ReactNode;
}>">Fragment</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>>Good to see you here.</<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>> </<data-lsp lsp="(alias) namespace React
import React">React</data-lsp>.<data-lsp lsp="const React.Fragment: React.ExoticComponent<{
    children?: React.ReactNode;
}>">Fragment</data-lsp>>);// 描画結果: <h1>Hello!</h1><h2>Good to see you here.</h2>`
```

ただ、より簡潔にフラグメントを表現するために`<>...</>`というショートハンド（短縮形）がよく使われます。次の例では、`<React.Fragment>`タグが`<>...</>`に置き換えられています。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = ( <> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>>Good to see you here.</<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>> </>);// 描画結果: <h1>Hello!</h1><h2>Good to see you here.</h2>`
```

```
tsx`const <data-lsp lsp="const element: React.JSX.Element">element</data-lsp> = ( <> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>>Good to see you here.</<data-lsp lsp="(property) JSX.IntrinsicElements.h2: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h2</data-lsp>> </>);// 描画結果: <h1>Hello!</h1><h2>Good to see you here.</h2>`
```

いずれの形式でも、フラグメントを使うことで`h1`と`h2`要素は同一階層に配置され、それらをラップする余計なHTML 要素を追加せずにレンダリングされます。フラグメントは、Reactアプリケーションのレンダリングパフォーマンスを持続的に向上させるツールとなります。

### JSX 内のコメント​

コメントはコードの読み易さを向上させる重要な要素です。しかし、JSX 内のコメントは少し特殊で、明示的にJavaScriptのブロック、つまり波カッコ `{}` 内に書く必要があります。

### 一行コメント​

JSX 内では一行コメントを書く方法は次の通りです。

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>{/* This is a comment */}</<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;// 描画結果: <div></div>`
```

```
tsx`const  <data-lsp lsp="const element: React.JSX.Element">element</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>{/* This is a comment */}</<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;// 描画結果: <div></div>`
```

このように、コメントは `{/* */}` の形式で書かれます。この書き方により、コメントはブラウザに表示されず、ただ開発者を支援するために存在します。

### ジェネリクス​

ジェネリクスを活用することで、一度定義したコンポーネントや関数を、各種の型に対応可能な形で再利用できます。ここではジェネリクス型を用いたReactコンポーネントの定義とその利用について、詳しく見ていきましょう。

## 📄️ ジェネリクス

型の安全性とコードの共通化の両立は難しいものです。あらゆる型で同じコードを使おうとすると、型の安全性が犠牲になります。逆に、型の安全性を重視しようとすると、同じようなコードを量産する必要が出てコードの共通化が達成しづらくなります。こうした問題を解決するために導入された言語機能がジェネリクスです。ジェネリクスを用いると、型の安全性とコードの共通化を両立することができます。

### 定义泛型组件​

首先，定义一个使用类型变量`T`的组件。在这里，创建一个名为`ItemType`的类型，并设计它通过属性`prop`接收类型`T`。

```
tsx`type  <data-lsp lsp="type ItemType<T> = {
    prop: T;
}">ItemType</data-lsp><<data-lsp lsp="(type parameter) T in type ItemType<T>">T</data-lsp>> = { <data-lsp lsp="(property) prop: T">prop</data-lsp>:  <data-lsp lsp="(type parameter) T in type ItemType<T>">T</data-lsp>;};const  <data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp>  = <<data-lsp lsp="(type parameter) T in <T>({ prop }: ItemType<T>): React.JSX.Element">T</data-lsp>,>({ <data-lsp lsp="(parameter) prop: T">prop</data-lsp> }:  <data-lsp lsp="type ItemType<T> = {
    prop: T;
}">ItemType</data-lsp><<data-lsp lsp="(type parameter) T in <T>({ prop }: ItemType<T>): React.JSX.Element">T</data-lsp>>) => <>{<data-lsp lsp="(parameter) prop: T">prop</data-lsp>}</>;`
```

```
tsx`type <data-lsp lsp="type ItemType<T> = {
    prop: T;
}">ItemType</data-lsp><<data-lsp lsp="(type parameter) T in type ItemType<T>">T</data-lsp>> = { <data-lsp lsp="(property) prop: T">prop</data-lsp>: <data-lsp lsp="(type parameter) T in type ItemType<T>">T</data-lsp>;};const <data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp> = <<data-lsp lsp="(type parameter) T in <T>({ prop }: ItemType<T>): React.JSX.Element">T</data-lsp>,>({ <data-lsp lsp="(parameter) prop: T">prop</data-lsp> }: <data-lsp lsp="type ItemType<T> = {
    prop: T;
}">ItemType</data-lsp><<data-lsp lsp="(type parameter) T in <T>({ prop }: ItemType<T>): React.JSX.Element">T</data-lsp>>) => <>{<data-lsp lsp="(parameter) prop: T">prop</data-lsp>}</>;`
```

对名为`Item`的组件应用泛型类型。因此，可以将任何类型作为`prop`接收。

关于`<T>`的写法，这里解释一下。如果仅写`<T>`作为泛型，TypeScript 可能会将其误认为是 JSX 标签。这是因为当 TypeScript 解析器读取`<T>`时，很难确定它是泛型开始还是 JSX 元素开始。为了避免这种混淆，必须在表示泛型开始的`<T>`后添加`,`，并写成`<T,>`。

### 使用泛型组件​

现在，让我们尝试使用上面定义的泛型类型组件。

```
tsx`const  <data-lsp lsp="const item1: React.JSX.Element">item1</data-lsp>  = <<data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp><string> <data-lsp lsp="(property) prop: string">prop</data-lsp>="a" />; // OKconst  <data-lsp lsp="const item2: React.JSX.Element">item2</data-lsp>  = <<data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp><number> <data-err><data-lsp lsp="(property) prop: number">prop</data-lsp></data-err>="a" />; // ErrorType 'string' is not assignable to type 'number'.2322Type 'string' is not assignable to type 'number'.`
```

```
tsx`const  <data-lsp lsp="const item1: React.JSX.Element">item1</data-lsp>  = <<data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp><string> <data-lsp lsp="(property) prop: string">prop</data-lsp>="a" />; // OKconst  <data-lsp lsp="const item2: React.JSX.Element">item2</data-lsp>  = <<data-lsp lsp="const Item: <T>({ prop }: ItemType<T>) => React.JSX.Element">Item</data-lsp><number> <data-err><data-lsp lsp="(property) prop: number">prop</data-lsp></data-err>="a" />; // ErrorType 'string' is not assignable to type 'number'.2322Type 'string' is not assignable to type 'number'.`
```

为`Item`组件传递`string`类型的类型参数，并将`a`作为其`prop`属性的字符串值。这是没有问题的。然而，在下一行中，为`Item`组件传递`number`类型的类型参数，但将`a`作为其`prop`属性的字符串值。这将导致 TypeScript 发出类型错误。这样可以确保类型安全性。

## JSX 的最佳实践

JSX 的最佳实践有助于编写有效且易读的代码。以下是一些主要的最佳实践。

### 组件名称始终以大写字母开头​

React 将以小写字母开头的组件视为 DOM 标签。因此，建议始终以大写字母开头命名组件。

```
tsx`// Goodconst  <data-lsp lsp="const MyComponent: () => React.JSX.Element">MyComponent</data-lsp>  = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp> />;};// Badconst  <data-lsp lsp="const myComponent: () => React.JSX.Element">myComponent</data-lsp>  = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp> />;};`
```

```
tsx`// Goodconst <data-lsp lsp="const MyComponent: () => React.JSX.Element">MyComponent</data-lsp> = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp> />;};// Badconst <data-lsp lsp="const myComponent: () => React.JSX.Element">myComponent</data-lsp> = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp> />;};`
```

### 使用括号括起来的多行 JSX​

推荐使用括号括起来的多行 JSX 以提高可读性。

```
tsx`// Goodconst  <data-lsp lsp="const Good: () => React.JSX.Element">Good</data-lsp>  = () => {  return ( <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> );};// Badconst  <data-lsp lsp="const Bad: () => React.JSX.Element">Bad</data-lsp>  = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;};`
```

```
tsx`// Goodconst <data-lsp lsp="const Good: () => React.JSX.Element">Good</data-lsp> = () => {  return ( <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> );};// Badconst <data-lsp lsp="const Bad: () => React.JSX.Element">Bad</data-lsp> = () => {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>> <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello, world!</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>> </<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;};`
```

### 使用自闭合标签​

通常，JSX 元素在开始标签和结束标签之间放置子元素。但是，如果内容为空，即没有子元素，则可以使用自闭合标签的简写形式。自闭合标签允许将开始标签和结束标签合并为一个标签。

以下两种表达方式是等效的：

```
tsx`// 長いバージョンconst  <data-lsp lsp="const a: React.JSX.Element">a</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>></<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>>;// 短いバージョン（自己終了タグ）const  <data-lsp lsp="const b: React.JSX.Element">b</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> />;`
```

```
tsx`// 長いバージョンconst  <data-lsp lsp="const a: React.JSX.Element">a</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>></<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>>;// 短いバージョン（自己終了タグ）const  <data-lsp lsp="const b: React.JSX.Element">b</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> />;`
```

在前一个示例中，明确写出了开始标签和结束标签，如`<input></input>`。而在后一个示例中，使用了自闭合标签，将开始标签和结束标签合并为`<input />`。这两种写法完全相同，但后一种形式更为简洁且更受欢迎。

### 在`true`的情况下可以省略布尔属性​

在 JSX 中，如果属性值为`true`，则可以通过仅写属性名来省略属性值。这种写法称为布尔属性。

以下两种表达方式是等效的：

```
tsx`// 長いバージョンconst  <data-lsp lsp="const a: React.JSX.Element">a</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>  <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.required?: boolean | undefined">required</data-lsp>={true} />;// 短いバージョン（真偽属性）const  <data-lsp lsp="const b: React.JSX.Element">b</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp>  <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.required?: boolean | undefined">required</data-lsp> />;`
```

```
tsx`// 長いバージョンconst  <data-lsp lsp="const a: React.JSX.Element">a</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.required?: boolean | undefined">required</data-lsp>={true} />;// 短いバージョン（真偽属性）const  <data-lsp lsp="const b: React.JSX.Element">b</data-lsp>  = <<data-lsp lsp="(property) JSX.IntrinsicElements.input: React.DetailedHTMLProps<React.InputHTMLAttributes<HTMLInputElement>, HTMLInputElement>">input</data-lsp> <data-lsp lsp="(property) React.InputHTMLAttributes<HTMLInputElement>.required?: boolean | undefined">required</data-lsp> />;`
```

在前一个示例中，对于名为`required`的属性，明确设置为`{true}`（即真）。而在后一个示例中，只需写属性名`required`即可表示属性为真。这两种写法完全相同，但后一种形式更为简洁且更受欢迎。

### 在映射函数中使用唯一的`key`属性​

使用`map`函数创建列表时，建议为每个元素添加唯一的`key`属性。这样 React 可以有效地应用更改、添加和删除。

```
tsx`const  <data-lsp lsp="const listItems: React.JSX.Element[]">listItems</data-lsp>  =  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.map<React.JSX.Element>(callbackfn: (value: number, index: number, array: number[]) => React.JSX.Element, thisArg?: any): React.JSX.Element[]">map</data-lsp>((<data-lsp lsp="(parameter) number: number">number</data-lsp>) => ( <<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>  <data-lsp lsp="(property) React.Attributes.key?: React.Key | null | undefined">key</data-lsp>={<data-lsp lsp="(parameter) number: number">number</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>()}>{<data-lsp lsp="(parameter) number: number">number</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>>));`
```

```
tsx`const  <data-lsp lsp="const listItems: React.JSX.Element[]">listItems</data-lsp>  =  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.map<React.JSX.Element>(callbackfn: (value: number, index: number, array: number[]) => React.JSX.Element, thisArg?: any): React.JSX.Element[]">map</data-lsp>((<data-lsp lsp="(parameter) number: number">number</data-lsp>) => ( <<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp> <data-lsp lsp="(property) React.Attributes.key?: React.Key | null | undefined">key</data-lsp>={<data-lsp lsp="(parameter) number: number">number</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>()}>{<data-lsp lsp="(parameter) number: number">number</data-lsp>}</<data-lsp lsp="(property) JSX.IntrinsicElements.li: React.DetailedHTMLProps<React.LiHTMLAttributes<HTMLLIElement>, HTMLLIElement>">li</data-lsp>>));`
```

## JSX 和编译​

由于 JSX 不是 JavaScript 的一部分，��此无法直接在浏览器中执行。默认情况下，JSX 语法不是 JavaScript 语法的一部分，因此直接执行浏览器无法理解。因此，必须将 JSX 编译（或转换）为 JavaScript。

在 TypeScript 中，为了指定这些 JSX 的编译方式，您需要在`tsconfig.json`文件中设置名为"jsx"的标志。该标志可以设置为以下 5 个值。

1.  "react"：选择此设置后，JSX 将被转换为 JavaScript。在生成的.js 文件中，每个 JSX 元素都将转换为相应的`React.createElement`调用。这指定了 React 库如何将 JSX 转换为标准 JavaScript。

1.  "react-jsx"：原始的 JSX 元素将被转换为`_jsx`调用，并包含在生成的.js 文件中。这有望提高一定程度的性能。

1.  "react-jsxdev"：这种模式也将原始的 JSX 元素转换为`_jsx`调用，但此模式仅用于开发环境。生成的`_jsx`调用包含额外的运行时检查，有助于简化开发中的调试。

1.  "preserve"：此模式将保留 JSX 的原始形式在输出文件中。换句话说，原始的 JSX 语法不会改变，期望输出的文件扩展名为.jsx。当需要保留 JSX 以供进一步转换（例如使用 Babel 等转译器）时使用。

1.  "react-native"：此选项也会直接输出 JSX。但是，期望输出的文件扩展名仍为.js。这主要用于 React Native 的开发环境。

通过上述设置，可以控制将 JSX 语法编译为 JavaScript 的方式。在同时使用 TypeScript 和 JSX 时，这些设置是必不可少的。

通过查看下面示例代码的编译结果，可以了解每个标志是如何编译的。

```
コンパイル前のTypeScripttsx`const  <data-lsp lsp="const HelloWorld: () => React.JSX.Element">HelloWorld</data-lsp>  = () => <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello world</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

```
コンパイル前のTypeScripttsx`const <data-lsp lsp="const HelloWorld: () => React.JSX.Element">HelloWorld</data-lsp> = () => <<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>Hello world</<data-lsp lsp="(property) JSX.IntrinsicElements.h1: React.DetailedHTMLProps<React.HTMLAttributes<HTMLHeadingElement>, HTMLHeadingElement>">h1</data-lsp>>;`
```

```
reactのコンパイル結果(JavaScriptコード)tsx`const  HelloWorld  = () =>  React.createElement("h1",  null,  "Hello world");`
```

```
reactのコンパイル結果(JavaScriptコード)tsx`const HelloWorld = () =>  React.createElement("h1",  null,  "Hello world");`
```

```
react-jsxのコンパイル結果(JavaScriptコード)tsx`const  HelloWorld  = () =>  _jsx("h1", { children:  "Hello world" });`
```

```
react-jsxのコンパイル結果(JavaScriptコード)tsx`const HelloWorld = () => _jsx("h1", { children:  "Hello world" });`
```

```
react-jsxdevのコンパイル結果(JavaScriptコード)tsx`const  HelloWorld  = () =>  _jsxDEV("h1", { children:  "Hello world" },  void  0,  false, { fileName: _jsxFileName, lineNumber:  3, columnNumber:  25 },  this);`
```

```
react-jsxdevのコンパイル結果(JavaScriptコード)tsx`const HelloWorld = () => _jsxDEV("h1", { children:  "Hello world" },  void  0,  false, { fileName: _jsxFileName, lineNumber:  3, columnNumber:  25 },  this);`
```

```
preserveのコンパイル結果(JavaScriptコード)tsx`const  HelloWorld  = () => <h1>Hello world</h1>;`
```

```
preserveのコンパイル結果(JavaScriptコード)tsx`const HelloWorld = () => <h1>Hello world</h1>;`
```

```
react-nativeのコンパイル結果(JavaScriptコード)tsx`const  HelloWorld  = () => <h1>Hello world</h1>;`
```

```
react-nativeのコンパイル結果(JavaScriptコード)tsx`const HelloWorld = () => <h1>Hello world</h1>;`
```
