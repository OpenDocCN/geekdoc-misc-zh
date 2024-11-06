# 索引:記号とキーワード

> 原文：[`typescriptbook.jp/symbols-and-keywords`](https://typescriptbook.jp/symbols-and-keywords)

JavaScriptやTypeScriptのコードには`?.`のような記号や`as`のようなキーワードが使われます。こういった記号やキーワードはGoogleで検索しづらく、意味を調べるのは難しいものです。

この索引は、JavaScriptとTypeScriptの記号やキーワードから、その名前や意味を調べられるようにするためのものです。コードを読んでいて未知の記号やキーワードに出くわしたら、その意味や使い方を調べる手がかりにしてください。

ここで扱う記号とキーワードには、JavaScript 由来のもの、つまり、JavaScriptとTypeScriptに共通して使えるものと、TypeScriptでのみ使えるものを併記しています。JavaScript 由来のものには![js](img/f2bff360fa9c865072b1586c301e7b00.png)のマークを、TypeScript 固有のものには![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)マークを表示しています。

## 記号​

### `!` 論理否定演算子 (logical not operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

真値と偽値を反転します。

### `!` 非 Nullアサーション (non-null assertion operator) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

値がnullやundefinedでないことを宣言し、コンパイラーに値を非 Nullとして解釈させます。

```
ts`function  <data-lsp lsp="function firstChar(text: string | undefined): string">firstChar</data-lsp>(<data-lsp lsp="(parameter) text: string | undefined">text</data-lsp>:  string  |  undefined) {  // コンパイルエラーにならない  return <data-lsp lsp="(parameter) text: string | undefined">text</data-lsp>!.<data-lsp lsp="(method) String.charAt(pos: number): string">charAt</data-lsp>(0);}`
```

```
ts`function <data-lsp lsp="function firstChar(text: string | undefined): string">firstChar</data-lsp>(<data-lsp lsp="(parameter) text: string | undefined">text</data-lsp>:  string  |  undefined) {  // コンパイルエラーにならない  return <data-lsp lsp="(parameter) text: string | undefined">text</data-lsp>!.<data-lsp lsp="(method) String.charAt(pos: number): string">charAt</data-lsp>(0);}`
```

### `!` 明確な割り当てアサーション演算子 (definite assignment assertion operator) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

クラスのプロパティが型アノテーションで示された型でセットされていることをコンパイラーに伝える記号です。

```
ts`class  <data-lsp lsp="class Example">Example</data-lsp> {  public <data-lsp lsp="(property) Example.foo: number">foo</data-lsp>!:  number;}`
```

```
ts`class <data-lsp lsp="class Example">Example</data-lsp> {  public <data-lsp lsp="(property) Example.foo: number">foo</data-lsp>!:  number;}`
```

または、変数の値が型アノテーションで示された型でセットされていることをコンパイラーに伝える記号です。

```
ts`let <data-lsp lsp="let numbers: number[]">numbers</data-lsp>!:  number[];`
```

```
ts`let <data-lsp lsp="let numbers: number[]">numbers</data-lsp>!:  number[];`
```

## 📄️ 明確な割り当てアサーション

明確な割り当てアサーションは、変数やプロパティが確実に初期化されていることをTypeScriptのコンパイラに伝える演算子です。

### `!!` Double Bang ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

double bangはJavaScriptで定義されている演算子ではなく、論理否定演算子を2つ連続したイディオムです。値がtruthyかを求めるときに使われます。

### `!=` 不等価演算子 (inequality operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値と右の値が異なるか判定します。型が異なる場合は型変換されて比較されます。

```
js`"1"  !=  1;false`
```

```
js`"1"  !=  1;false`
```

### `!==` 厳密不等価演算子 (strict inequality operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

型を含めて左の値と右の値が異なるか判定します。

```
js`1  !==  "1";true`
```

```
js`1  !==  "1";true`
```

### `"` 文字列リテラル (string literal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

`"foo"`のように文字列リテラルの開始と終了に使われる記号です。

### `#` プライベートプロパティ (private property) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

クラスのプロパティのうち`#`で始まるプロパティはプライベートになります。

```
js`class  <data-lsp lsp="class ExampleClass">ExampleClass</data-lsp> { #privateField; #privateMethod() {}  static #PRIVATE_STATIC_FIELD;  static #privateStaticMethod() {}}`
```

```
js`class <data-lsp lsp="class ExampleClass">ExampleClass</data-lsp> { #privateField; #privateMethod() {}  static #PRIVATE_STATIC_FIELD;  static #privateStaticMethod() {}}`
```

### `$` ドル変数 (dollar variable) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

慣習的にjQueryなどのライブラリで変数として使われることがあります。変数名として`$`が使われる場合は、JavaScriptとしては変数以上の特別な意味はありません。

### `$` 文字列中の変数展開 (placeholder) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

テンプレートリテラル内で変数を展開するときに用いられる記号です。

```
js`const  <data-lsp lsp="const name: &quot;John&quot;">name</data-lsp>  =  "John";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Hi, ${<data-lsp lsp="const name: void">name</data-lsp>}.`);"Hi, John."`
```

```
js`const  <data-lsp lsp="const name: &quot;John&quot;">name</data-lsp>  =  "John";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Hi, ${<data-lsp lsp="const name: void">name</data-lsp>}.`);"Hi, John."`
```

### `%` 剰余演算子 (reminder operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値を右の値で割った余りを計算します。

```
js`12  %  5;2`
```

```
js`12  %  5;2`
```

### `%=` 剰余代入 (reminder assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値に右の値で割り算した余りを左の変数に割り当てます。

### `&` ビット論理積 (bitwise and) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値と右の値で共にビットが1である位置のビットを1に します。

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> & <data-lsp lsp="const b: 5">b</data-lsp>);00000001// 出力: 1`
```

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> & <data-lsp lsp="const b: 5">b</data-lsp>);00000001// 出力: 1`
```

### `&` インターセクション型 (intersection type) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

複数の型を組み合わせたインターセクション型を定義します。

```
ts`interface  <data-lsp lsp="interface Swordsman">Swordsman</data-lsp> { <data-lsp lsp="(property) Swordsman.sword: string">sword</data-lsp>:  string;}interface  <data-lsp lsp="interface Wizard">Wizard</data-lsp> { <data-lsp lsp="(property) Wizard.magic: string">magic</data-lsp>:  string;}type  <data-lsp lsp="type MagicalSwordsman = Swordsman &amp; Wizard">MagicalSwordsman</data-lsp>  =  <data-lsp lsp="interface Swordsman">Swordsman</data-lsp>  &  <data-lsp lsp="interface Wizard">Wizard</data-lsp>;`
```

```
ts`interface <data-lsp lsp="interface Swordsman">Swordsman</data-lsp> { <data-lsp lsp="(property) Swordsman.sword: string">sword</data-lsp>:  string;}interface <data-lsp lsp="interface Wizard">Wizard</data-lsp> { <data-lsp lsp="(property) Wizard.magic: string">magic</data-lsp>:  string;}type <data-lsp lsp="type MagicalSwordsman = Swordsman &amp; Wizard">MagicalSwordsman</data-lsp> = <data-lsp lsp="interface Swordsman">Swordsman</data-lsp> & <data-lsp lsp="interface Wizard">Wizard</data-lsp>;`
```

## 📄️ インターセクション型

考え方はユニオン型と相対するものです。ユニオン型がどれかを意味するならインターセクション型はどれもです。言い換えるとオブジェクトの定義を合成させることを指します。

### `&=` ビット論理積代入 (bitwise and assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値と右の値で共にビットが1である位置のビットを1にした結果を左の変数に割り当てます。

```
js`let <data-lsp lsp="let a: number">a</data-lsp> =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="let a: number">a</data-lsp> &= <data-lsp lsp="const b: 5">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: number">a</data-lsp>);00000001// 出力: 1`
```

```
js`let <data-lsp lsp="let a: number">a</data-lsp> =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="let a: number">a</data-lsp> &= <data-lsp lsp="const b: 5">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: number">a</data-lsp>);00000001// 出力: 1`
```

### `&&` 論理積 (logical and) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値がtruthyな場合は右の値を返します。そうでないときは左の値を返します。

特にboolean 値が与えられた場合は、双方とも`true`のときに`true`を返し、そうでないときに`false`を返します。

```
js`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  &&  true);true<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  &&  false);false<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(1  &&  "");""`
```

```
js`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  &&  true);true<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  &&  false);false<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(1  &&  "");""`
```

### `&&=` 論理積代入 (logical and assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数と右の値の`&&`論理積の結果を左の変数に割り当てます。

```
js`let <data-lsp lsp="let a: boolean">a</data-lsp> =  true;let <data-lsp lsp="let b: number">b</data-lsp> =  1;<data-lsp lsp="let a: boolean">a</data-lsp> &&= <data-lsp lsp="let b: number">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: boolean">a</data-lsp>);1`
```

```
js`let <data-lsp lsp="let a: boolean">a</data-lsp> =  true;let <data-lsp lsp="let b: number">b</data-lsp> =  1;<data-lsp lsp="let a: boolean">a</data-lsp> &&= <data-lsp lsp="let b: number">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: boolean">a</data-lsp>);1`
```

### `'` 文字列リテラル (string literal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

`'foo'`のように文字列リテラルの開始と終了に使われる記号です。

### `()` 即時実行関数の一部 (IIFE: immediately invoked function expression) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

定義されるとすぐ実行される即時実行関数式(IIFE; Immediately Invoked Function Expression)の一部に用いられる書き方です。即時実行関数式そのものがデザインパターンで、その一部である`()`は関数呼び出しのカッコであり、JavaScriptの特別な演算子や構文というわけではありません。即時実行関数式は即時関数と呼ばれることがあります。

```
js`(function () {})();//              ^^(function () {})();//              ^^(() => {})();//        ^^`
```

```
js`(function () {})();//              ^^(function () {})();//              ^^(() => {})();//        ^^`
```

### `*` 乗算演算子 (multiplication operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値と右の値を掛け算します。

### `*` ジェネレーター関数の宣言 (generator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

`Generator`オブジェクトを返すジェネレーター関数を宣言するときに用いられる記号です。

```
js`function*  <data-lsp lsp="function numberGenerator(): Generator<1 | 2, void, unknown>">numberGenerator</data-lsp>() {  yield  1;  yield  2;  yield  2;}`
```

```
js`function* <data-lsp lsp="function numberGenerator(): Generator<1 | 2, void, unknown>">numberGenerator</data-lsp>() {  yield  1;  yield  2;  yield  2;}`
```

### `*` yield*式 (yield) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

別のジェネレーターに移譲する式を書くときに用いられる記号です。

```
js`function*  <data-lsp lsp="function func1(): Generator<number, void, unknown>">func1</data-lsp>() {  yield  123;}function*  <data-lsp lsp="function func2(): Generator<number, void, unknown>">func2</data-lsp>() {  yield*  <data-lsp lsp="function func1(): Generator<number, void, unknown>">func1</data-lsp>();  //   ^ここ}`
```

```
js`function* <data-lsp lsp="function func1(): Generator<number, void, unknown>">func1</data-lsp>() {  yield  123;}function* <data-lsp lsp="function func2(): Generator<number, void, unknown>">func2</data-lsp>() {  yield* <data-lsp lsp="function func1(): Generator<number, void, unknown>">func1</data-lsp>();  //   ^ここ}`
```

### `*=` 乗算代入 (multiplication assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値と右の値を掛け算した結果を左の変数に割り当てます。

### `**` べき乗演算子 (exponentiation) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値を右の値でべき乗します。

```
js`2  **  3;8`
```

```
js`2  **  3;8`
```

### `**=` べき乗代入 (exponentiation assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値を右の値でべき乗した結果を左の変数に割り当てます。

### `+` 単項正値演算子 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

number 型に変換します。

```
js`+"1";1`
```

```
js`+"1";1`
```

### `+` 加算演算子 (addition operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

2つの値を足し算します。

### `+` 文字列結合演算子 (concatenation operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

2つの文字列を結合します。

### `+` 修飾子の付加 ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

`readonly`や`?`などの修飾子を追加します。

何も指定しない場合は暗黙的に`+`が付与されるので`+`を実際に利用する機会はおそらくありません。

```
ts`type  <data-lsp lsp="type MyPartial<T> = { [k in keyof T]+?: T[k] | undefined; }">MyPartial</data-lsp><<data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>> = { [<data-lsp lsp="(type parameter) k">k</data-lsp>  in  keyof  <data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>]+?:  <data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};type  <data-lsp lsp="type MyReadonly<T> = { +readonly [k in keyof T]: T[k]; }">MyReadonly</data-lsp><<data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>> = {  +readonly [<data-lsp lsp="(type parameter) k">k</data-lsp>  in  keyof  <data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>]:  <data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};`
```

```
ts`type <data-lsp lsp="type MyPartial<T> = { [k in keyof T]+?: T[k] | undefined; }">MyPartial</data-lsp><<data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>> = { [<data-lsp lsp="(type parameter) k">k</data-lsp> in  keyof <data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>]+?: <data-lsp lsp="(type parameter) T in type MyPartial<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};type <data-lsp lsp="type MyReadonly<T> = { +readonly [k in keyof T]: T[k]; }">MyReadonly</data-lsp><<data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>> = {  +readonly [<data-lsp lsp="(type parameter) k">k</data-lsp> in  keyof <data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>]: <data-lsp lsp="(type parameter) T in type MyReadonly<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};`
```

### `+=` 加算代入 (addition assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値とに右の値を足し算した結果を左の変数に割り当てます。

### `++` インクリメント (increment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

変数に`1`を足す演算子です。

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  3;<data-lsp lsp="let x: number">x</data-lsp>++;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let x: number">x</data-lsp>);4`
```

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  3;<data-lsp lsp="let x: number">x</data-lsp>++;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let x: number">x</data-lsp>);4`
```

### `,` 関数引数の区切り ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

複数の引数を関数に与えたり、複数の引数を受け取る関数宣言に用いる記号です。

```
js`function  <data-lsp lsp="function plus(x: any, y: any, z: any): any">plus</data-lsp>(<data-lsp lsp="(parameter) x: any">x</data-lsp>, <data-lsp lsp="(parameter) y: any">y</data-lsp>, <data-lsp lsp="(parameter) z: any">z</data-lsp>) {  return <data-lsp lsp="(parameter) x: any">x</data-lsp> + <data-lsp lsp="(parameter) y: any">y</data-lsp> + <data-lsp lsp="(parameter) z: any">z</data-lsp>;}<data-lsp lsp="function plus(x: any, y: any, z: any): any">plus</data-lsp>(1,  2,  3);`
```

```
js`function <data-lsp lsp="function plus(x: any, y: any, z: any): any">plus</data-lsp>(<data-lsp lsp="(parameter) x: any">x</data-lsp>, <data-lsp lsp="(parameter) y: any">y</data-lsp>, <data-lsp lsp="(parameter) z: any">z</data-lsp>) {  return <data-lsp lsp="(parameter) x: any">x</data-lsp> + <data-lsp lsp="(parameter) y: any">y</data-lsp> + <data-lsp lsp="(parameter) z: any">z</data-lsp>;}<data-lsp lsp="function plus(x: any, y: any, z: any): any">plus</data-lsp>(1,  2,  3);`
```

### `,` 配列要素の区切り ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

複数の要素を持つ配列を宣言するときに用いる記号です。

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];`
```

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];`
```

### `,` オブジェクトプロパティの区切り ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

複数のプロパティを持つオブジェクトを宣言するときに用いる記号です。

```
js`const  <data-lsp lsp="const data: {
    property1: number;
    property2: boolean;
    property3: string;
}">data</data-lsp>  = { <data-lsp lsp="(property) property1: number">property1</data-lsp>:  1, <data-lsp lsp="(property) property2: boolean">property2</data-lsp>:  true, <data-lsp lsp="(property) property3: string">property3</data-lsp>:  "hello",};`
```

```
js`const  <data-lsp lsp="const data: {
    property1: number;
    property2: boolean;
    property3: string;
}">data</data-lsp>  = { <data-lsp lsp="(property) property1: number">property1</data-lsp>:  1, <data-lsp lsp="(property) property2: boolean">property2</data-lsp>:  true, <data-lsp lsp="(property) property3: string">property3</data-lsp>:  "hello",};`
```

### `,` タプル型の要素の区切り ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

複数の要素を持つタプル型を宣言するときに用いる記号です。

```
ts`type  <data-lsp lsp="type Tuple = [number, string, boolean]">Tuple</data-lsp>  = [number,  string,  boolean];`
```

```
ts`type <data-lsp lsp="type Tuple = [number, string, boolean]">Tuple</data-lsp> = [number,  string,  boolean];`
```

### `,` カンマ演算子 (comma operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左から右に式を評価をして、一番右の評価した値を返します。

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  -1;const  <data-lsp lsp="const a: boolean">a</data-lsp>  = (<data-lsp lsp="let x: number">x</data-lsp>++, <data-lsp lsp="let x: number">x</data-lsp>++, <data-lsp lsp="let x: number">x</data-lsp> >  0);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: boolean">a</data-lsp>);true`
```

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  -1;const  <data-lsp lsp="const a: boolean">a</data-lsp>  = (<data-lsp lsp="let x: number">x</data-lsp>++, <data-lsp lsp="let x: number">x</data-lsp>++, <data-lsp lsp="let x: number">x</data-lsp> >  0);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: boolean">a</data-lsp>);true`
```

### `-` 単項負値演算子 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

正負を反転してnumber 型に変換します。

```
js`-"1";-1`
```

```
js`-"1";-1`
```

### `-` 減算演算子 (subtraction operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

2つの値を引き算します。

### `-` 修飾子の削除 ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

`readonly`や`?`などの修飾子を削除します。

```
ts`type  <data-lsp lsp="type MyRequired<T> = { [k in keyof T]-?: T[k]; }">MyRequired</data-lsp><<data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>> = { [<data-lsp lsp="(type parameter) k">k</data-lsp>  in  keyof  <data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>]-?:  <data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};type  <data-lsp lsp="type Writable<T> = { -readonly [k in keyof T]: T[k]; }">Writable</data-lsp><<data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>> = {  -readonly [<data-lsp lsp="(type parameter) k">k</data-lsp>  in  keyof  <data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>]:  <data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};`
```

```
ts`type <data-lsp lsp="type MyRequired<T> = { [k in keyof T]-?: T[k]; }">MyRequired</data-lsp><<data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>> = { [<data-lsp lsp="(type parameter) k">k</data-lsp> in  keyof <data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>]-?: <data-lsp lsp="(type parameter) T in type MyRequired<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};type <data-lsp lsp="type Writable<T> = { -readonly [k in keyof T]: T[k]; }">Writable</data-lsp><<data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>> = {  -readonly [<data-lsp lsp="(type parameter) k">k</data-lsp> in  keyof <data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>]: <data-lsp lsp="(type parameter) T in type Writable<T>">T</data-lsp>[<data-lsp lsp="(type parameter) k">k</data-lsp>];};`
```

### `-=` 減算代入 (subtraction assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値から右の値を引き算した結果を左の変数に割り当てます。

### `--` デクリメント (decrement) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

変数に`1`を引き算する演算子です。

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  3;<data-lsp lsp="let x: number">x</data-lsp>--;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let x: number">x</data-lsp>);2`
```

```
js`let <data-lsp lsp="let x: number">x</data-lsp> =  3;<data-lsp lsp="let x: number">x</data-lsp>--;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let x: number">x</data-lsp>);2`
```

### `.` プロパティへのアクセス (dot operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトのプロパティにアクセスするときに用いる記号です。

```
js`const  <data-lsp lsp="const object: {
    property: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) property: number">property</data-lsp>:  123 };<data-lsp lsp="const object: {
    property: number;
}">object</data-lsp>.<data-lsp lsp="(property) property: number">property</data-lsp>;123`
```

```
js`const  <data-lsp lsp="const object: {
    property: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) property: number">property</data-lsp>:  123 };<data-lsp lsp="const object: {
    property: number;
}">object</data-lsp>.<data-lsp lsp="(property) property: number">property</data-lsp>;123`
```

### `...` スプレッド構文 (spread syntax) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

配列などの反復可能オブジェクトを関数の引数にする構文です。

```
js`function  <data-lsp lsp="function sum(x: any, y: any, z: any): any">sum</data-lsp>(<data-lsp lsp="(parameter) x: any">x</data-lsp>, <data-lsp lsp="(parameter) y: any">y</data-lsp>, <data-lsp lsp="(parameter) z: any">z</data-lsp>) {  return <data-lsp lsp="(parameter) x: any">x</data-lsp> + <data-lsp lsp="(parameter) y: any">y</data-lsp> + <data-lsp lsp="(parameter) z: any">z</data-lsp>;}const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function sum(x: any, y: any, z: any): any">sum</data-lsp>(...<data-lsp lsp="const numbers: number[]">numbers</data-lsp>));6`
```

```
js`function <data-lsp lsp="function sum(x: any, y: any, z: any): any">sum</data-lsp>(<data-lsp lsp="(parameter) x: any">x</data-lsp>, <data-lsp lsp="(parameter) y: any">y</data-lsp>, <data-lsp lsp="(parameter) z: any">z</data-lsp>) {  return <data-lsp lsp="(parameter) x: any">x</data-lsp> + <data-lsp lsp="(parameter) y: any">y</data-lsp> + <data-lsp lsp="(parameter) z: any">z</data-lsp>;}const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function sum(x: any, y: any, z: any): any">sum</data-lsp>(...<data-lsp lsp="const numbers: number[]">numbers</data-lsp>));6`
```

または、配列などの反復可能オブジェクトを配列要素に展開する構文です。

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const  <data-lsp lsp="const newNumbers: number[]">newNumbers</data-lsp>  = [0,  ...<data-lsp lsp="const numbers: number[]">numbers</data-lsp>,  4];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const newNumbers: number[]">newNumbers</data-lsp>);[ 0, 1, 2, 3, 4 ]`
```

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const  <data-lsp lsp="const newNumbers: number[]">newNumbers</data-lsp>  = [0,  ...<data-lsp lsp="const numbers: number[]">numbers</data-lsp>,  4];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const newNumbers: number[]">newNumbers</data-lsp>);[ 0, 1, 2, 3, 4 ]`
```

または、オブジェクトのプロパティを展開する構文です。

```
js`const  <data-lsp lsp="const object: {
    x: number;
    y: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) x: number">x</data-lsp>:  1, <data-lsp lsp="(property) y: number">y</data-lsp>:  2 };const  <data-lsp lsp="const newObject: {
    z: number;
    x: number;
    y: number;
}">newObject</data-lsp>  = { ...<data-lsp lsp="const object: {
    x: number;
    y: number;
}">object</data-lsp>, <data-lsp lsp="(property) z: number">z</data-lsp>:  3 };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const newObject: {
    z: number;
    x: number;
    y: number;
}">newObject</data-lsp>);{ x: 1, y: 2, z: 3 }`
```

```
js`const  <data-lsp lsp="const object: {
    x: number;
    y: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) x: number">x</data-lsp>:  1, <data-lsp lsp="(property) y: number">y</data-lsp>:  2 };const  <data-lsp lsp="const newObject: {
    z: number;
    x: number;
    y: number;
}">newObject</data-lsp>  = { ...<data-lsp lsp="const object: {
    x: number;
    y: number;
}">object</data-lsp>, <data-lsp lsp="(property) z: number">z</data-lsp>:  3 };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const newObject: {
    z: number;
    x: number;
    y: number;
}">newObject</data-lsp>);{ x: 1, y: 2, z: 3 }`
```

### `...` 残余構文 (rest syntax) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

関数の残りの引数をひとつの配列として受け取るのに用いられる構文です。

```
js`function  <data-lsp lsp="function func(a: any, b: any, ...rest: any[]): any[]">func</data-lsp>(<data-lsp lsp="(parameter) a: any">a</data-lsp>, <data-lsp lsp="(parameter) b: any">b</data-lsp>,  ...<data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>) {  return <data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function func(a: any, b: any, ...rest: any[]): any[]">func</data-lsp>(1,  2,  3,  4,  5));[ 3, 4, 5 ]`
```

```
js`function <data-lsp lsp="function func(a: any, b: any, ...rest: any[]): any[]">func</data-lsp>(<data-lsp lsp="(parameter) a: any">a</data-lsp>, <data-lsp lsp="(parameter) b: any">b</data-lsp>,  ...<data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>) {  return <data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function func(a: any, b: any, ...rest: any[]): any[]">func</data-lsp>(1,  2,  3,  4,  5));[ 3, 4, 5 ]`
```

または、配列などの反復可能オブジェクトの残りの要素を取り出す構文です。

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3,  4,  5];const [<data-lsp lsp="const first: number">first</data-lsp>,  <data-lsp lsp="const second: number">second</data-lsp>,  ...<data-lsp lsp="const rest: number[]">rest</data-lsp>] = <data-lsp lsp="const numbers: number[]">numbers</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rest: number[]">rest</data-lsp>);[ 3, 4, 5 ]`
```

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3,  4,  5];const [<data-lsp lsp="const first: number">first</data-lsp>,  <data-lsp lsp="const second: number">second</data-lsp>,  ...<data-lsp lsp="const rest: number[]">rest</data-lsp>] = <data-lsp lsp="const numbers: number[]">numbers</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rest: number[]">rest</data-lsp>);[ 3, 4, 5 ]`
```

または、オブジェクトの残りのプロパティを取り出す構文です。

```
js`const  <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3, <data-lsp lsp="(property) d: number">d</data-lsp>:  4 };const { <data-lsp lsp="const a: number">a</data-lsp>,  <data-lsp lsp="const b: number">b</data-lsp>,  ...<data-lsp lsp="const rest: {
    c: number;
    d: number;
}">rest</data-lsp> } = <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rest: {
    c: number;
    d: number;
}">rest</data-lsp>);{ c: 3, d: 4 }`
```

```
js`const  <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3, <data-lsp lsp="(property) d: number">d</data-lsp>:  4 };const { <data-lsp lsp="const a: number">a</data-lsp>,  <data-lsp lsp="const b: number">b</data-lsp>,  ...<data-lsp lsp="const rest: {
    c: number;
    d: number;
}">rest</data-lsp> } = <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const rest: {
    c: number;
    d: number;
}">rest</data-lsp>);{ c: 3, d: 4 }`
```

### `/` 除算演算子 (division operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値を右の値で割り算します。

### `/` 正規表現リテラル (regular expression literal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

`/[0-9]+/`のような正規表現リテラルの前後に書かれる記号です。

### `/=` 除算代入 (division assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値を右の値で割り算した結果を左の変数に割り当てます。

### `//` 一行コメント (one line comment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

行コメントの開始を表す記号です。

### `/*` 複数行コメント (multiline comment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

複数行コメントの開始を表す記号です。

```
js`/* コメント */`
```

```
js`/* コメント */`
```

### `/**` JSDoc​

慣習的にJSDocなどのドキュメンテーションコメントの開始を表す記号です。これはJavaScriptやTypeScriptの構文ではなく、複数行コメントを用いたドキュメンテーションに慣習的に用いられるものです。

### `:` オブジェクトの一部 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトプロパティのキーと値の対関係を表すのに用いられる記号です。

```
js`const  <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3, <data-lsp lsp="(property) d: number">d</data-lsp>:  4 };`
```

```
js`const  <data-lsp lsp="const object: {
    a: number;
    b: number;
    c: number;
    d: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3, <data-lsp lsp="(property) d: number">d</data-lsp>:  4 };`
```

### `:` 三項演算子の一部 (conditional operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

`a ? b : c`のような三項演算子のelseを表すのに用いられる記号です。

### `:` 型アノテーション (type annotation) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

変数の型アノテーションに用いられる記号です。

```
ts`const  <data-lsp lsp="const variable: number">variable</data-lsp>:  number  =  20;`
```

```
ts`const  <data-lsp lsp="const variable: number">variable</data-lsp>:  number  =  20;`
```

または、関数の引数や戻り値の型アノテーションに用いられる記号です。

```
ts`function  <data-lsp lsp="function numberToString(x: number): string">numberToString</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number):  string {  return  <data-lsp lsp="(parameter) x: number">x</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>();}`
```

```
ts`function <data-lsp lsp="function numberToString(x: number): string">numberToString</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number):  string {  return  <data-lsp lsp="(parameter) x: number">x</data-lsp>.<data-lsp lsp="(method) Number.toString(radix?: number | undefined): string">toString</data-lsp>();}`
```

### `<` 小なり演算子 (less than operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値が右の値よりも小さいか判定します。

### `<` ジェネリクス (generic) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

ジェネリクスの型引数の開始に用いられる記号です。

```
ts`function  <data-lsp lsp="function func<T>(x: T): void">func</data-lsp><<data-lsp lsp="(type parameter) T in func<T>(x: T): void">T</data-lsp>>(<data-lsp lsp="(parameter) x: T">x</data-lsp>:  <data-lsp lsp="(type parameter) T in func<T>(x: T): void">T</data-lsp>) {}const  <data-lsp lsp="const result: void">result</data-lsp>  =  <data-lsp lsp="function func<string>(x: string): void">func</data-lsp><string>("hello");`
```

```
ts`function <data-lsp lsp="function func<T>(x: T): void">func</data-lsp><<data-lsp lsp="(type parameter) T in func<T>(x: T): void">T</data-lsp>>(<data-lsp lsp="(parameter) x: T">x</data-lsp>: <data-lsp lsp="(type parameter) T in func<T>(x: T): void">T</data-lsp>) {}const  <data-lsp lsp="const result: void">result</data-lsp>  = <data-lsp lsp="function func<string>(x: string): void">func</data-lsp><string>("hello");`
```

## 📄️ ジェネリクス

型の安全性とコードの共通化の両立は難しいものです。あらゆる型で同じコードを使おうとすると、型の安全性が犠牲になります。逆に、型の安全性を重視しようとすると、同じようなコードを量産する必要が出てコードの共通化が達成しづらくなります。こうした問題を解決するために導入された言語機能がジェネリクスです。ジェネリクスを用いると、型の安全性とコードの共通化を両立することができます。

### `<` JSX ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

JSXと呼ばれるXMLリテラルの開始に現れる記号です。

```
Hello.tsxtsx`function  <data-lsp lsp="function Hello(): React.JSX.Element">Hello</data-lsp>() {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>HELLO</<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;}`
```

```
Hello.tsxtsx`function <data-lsp lsp="function Hello(): React.JSX.Element">Hello</data-lsp>() {  return <<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>HELLO</<data-lsp lsp="(property) JSX.IntrinsicElements.div: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>">div</data-lsp>>;}`
```

### `<` 型アサーション (type assertion) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

型アサーションに用いられる記号です。`as`の別の書き方です。

```
ts`let <data-lsp lsp="let someValue: unknown">someValue</data-lsp>:  unknown  =  "this is a string";let <data-lsp lsp="let strLength: number">strLength</data-lsp>:  number  = (<string><data-lsp lsp="let someValue: unknown">someValue</data-lsp>).<data-lsp lsp="(property) String.length: number">length</data-lsp>;`
```

```
ts`let <data-lsp lsp="let someValue: unknown">someValue</data-lsp>:  unknown  =  "this is a string";let <data-lsp lsp="let strLength: number">strLength</data-lsp>:  number  = (<string><data-lsp lsp="let someValue: unknown">someValue</data-lsp>).<data-lsp lsp="(property) String.length: number">length</data-lsp>;`
```

### `<=` 小なりイコール演算子 (less than or equal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値が右の値以下か判定します。

### `<<` ビット左シフト演算子 (left shift operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値のビットを右の値の数だけ左にずらします。

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> << <data-lsp lsp="const b: 3">b</data-lsp>);00001000// 出力: 8`
```

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> << <data-lsp lsp="const b: 3">b</data-lsp>);00001000// 出力: 8`
```

### `<<=` 左シフト代入 (left shift assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値のビットを右の値の数だけ左にずらした結果を左の変数に割り当てます。

```
js`let <data-lsp lsp="let a: number">a</data-lsp> =  1;00000001const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="let a: number">a</data-lsp> <<= <data-lsp lsp="const b: 3">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: number">a</data-lsp>);00001000// 出力: 8`
```

```
js`let <data-lsp lsp="let a: number">a</data-lsp> =  1;00000001const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="let a: number">a</data-lsp> <<= <data-lsp lsp="const b: 3">b</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: number">a</data-lsp>);00001000// 出力: 8`
```

### `=` 代入演算子 (assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数に右の値を割り当てます。

### `==` 等価演算子 (equality) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値と右の値が等しいか判定します。型が異なる場合は型変換されて比較されます。

```
js`"1"  ==  1;true`
```

```
js`"1"  ==  1;true`
```

### `===` 厳密等価演算子 (strict equality) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

型を含めて左の値と右の値が等しいか判定します。

```
js`"1"  ===  1;false`
```

```
js`"1"  ===  1;false`
```

### `=>` アロー関数の一部 (arrow function) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

アロー関数の引数と関数ボディーの間に書かれる記号です。

```
js`const  <data-lsp lsp="const increment: (num: any) => any">increment</data-lsp>  = (<data-lsp lsp="(parameter) num: any">num</data-lsp>) => <data-lsp lsp="(parameter) num: any">num</data-lsp> +  1;`
```

```
js`const <data-lsp lsp="const increment: (num: any) => any">increment</data-lsp> = (<data-lsp lsp="(parameter) num: any">num</data-lsp>) => <data-lsp lsp="(parameter) num: any">num</data-lsp> +  1;`
```

### `>` 大なり演算子 (greater than) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値が右の値よりも大きいか判定します。

### `>=` 大なりイコール演算子 (greater than or equal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値が右の値以上か判定します。

### `>>` ビット右シフト演算子 (right shift) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値のビットを右の値の数だけ右にずらします。

```
js`const  <data-lsp lsp="const a: 8">a</data-lsp>  =  8;00001000const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 8">a</data-lsp> >> <data-lsp lsp="const b: 3">b</data-lsp>);00000001// 出力: 1`
```

```
js`const  <data-lsp lsp="const a: 8">a</data-lsp>  =  8;00001000const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 8">a</data-lsp> >> <data-lsp lsp="const b: 3">b</data-lsp>);00000001// 出力: 1`
```

### `>>=` 右シフト代入 (right shift assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値のビットを右の値の数だけ右にずらした結果を左の変数に割り当てます。

### `>>>` 符号なし右シフト演算子 (unsigned right shift) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値のビットを右の値の数だけ右にずらします。左に入る符号ビットは常に0になります。

```
js`const  <data-lsp lsp="const a: -2">a</data-lsp>  =  -2;11111111111111111111111111111110const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: -2">a</data-lsp> >>> <data-lsp lsp="const b: 3">b</data-lsp>);00011111111111111111111111111111// 出力: 536870911`
```

```
js`const  <data-lsp lsp="const a: -2">a</data-lsp>  =  -2;11111111111111111111111111111110const  <data-lsp lsp="const b: 3">b</data-lsp>  =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: -2">a</data-lsp> >>> <data-lsp lsp="const b: 3">b</data-lsp>);00011111111111111111111111111111// 出力: 536870911`
```

### `>>>=` 符号なし右シフト代入 (unsigned right shift assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値のビットを右の値の数だけ右にずらした結果を左の変数に割り当てます。左に入る符号ビットは常に0になります。

### `?` 三項演算子の一部 (conditional operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

三項演算子`a ? b : c`の一部で、条件式の終わりに置かれる記号です。

### `?` 可选修饰符（optional property） ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

将对象的属性定义为可选属性。

```
ts`interface  <data-lsp lsp="interface User">User</data-lsp> { <data-lsp lsp="(property) User.name: string">name</data-lsp>:  string;  // name は必須 <data-lsp lsp="(property) User.age?: number | undefined">age</data-lsp>?:  number;  // age は任意}const  <data-lsp lsp="const user: User">user</data-lsp>:  <data-lsp lsp="interface User">User</data-lsp>  = { <data-lsp lsp="(property) User.name: string">name</data-lsp>:  "taro" };`
```

```
ts`interface <data-lsp lsp="interface User">User</data-lsp> { <data-lsp lsp="(property) User.name: string">name</data-lsp>:  string;  // name は必須 <data-lsp lsp="(property) User.age?: number | undefined">age</data-lsp>?:  number;  // age は任意}const  <data-lsp lsp="const user: User">user</data-lsp>: <data-lsp lsp="interface User">User</data-lsp> = { <data-lsp lsp="(property) User.name: string">name</data-lsp>:  "taro" };`
```

或者，使函数参数不是必需的。

```
ts`function  <data-lsp lsp="function func(x?: number): void">func</data-lsp>(<data-lsp lsp="(parameter) x: number | undefined">x</data-lsp>?:  number) {}<data-lsp lsp="function func(x?: number): void">func</data-lsp>();// xがなくてもOK`
```

```
ts`function <data-lsp lsp="function func(x?: number): void">func</data-lsp>(<data-lsp lsp="(parameter) x: number | undefined">x</data-lsp>?:  number) {}<data-lsp lsp="function func(x?: number): void">func</data-lsp>();// xがなくてもOK`
```

### `?.` 可选链（optional chaining） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

当属性访问源为`null`或`undefined`时不引发错误并返回`undefined`。

```
js`const  <data-lsp lsp="const user: null">user</data-lsp>  =  null;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user: null">user</data-lsp>.<data-lsp lsp="any">name</data-lsp>);Cannot read property 'name' of null<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user: null">user</data-lsp>?.<data-lsp lsp="any">name</data-lsp>);undefined`
```

```
js`const  <data-lsp lsp="const user: null">user</data-lsp>  =  null;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user: null">user</data-lsp>.<data-lsp lsp="any">name</data-lsp>);Cannot read property 'name' of null<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user: null">user</data-lsp>?.<data-lsp lsp="any">name</data-lsp>);undefined`
```

### `??` Null 合体（nullish coalescing operator） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

当左值为`null`或`undefined`时返回右值，否则返回左值。

```
js`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var undefined">undefined</data-lsp>  ??  1);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(2  ??  1);2`
```

```
js`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var undefined">undefined</data-lsp>  ??  1);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(2  ??  1);2`
```

### `??=` Null 合体代入（logical nullish assignment） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

当左边的值为`null`或`undefined`时才将右边的值分配给左边的变量。

```
js`const  <data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>  = { <data-lsp lsp="(property) name: undefined">name</data-lsp>:  <data-lsp lsp="var undefined">undefined</data-lsp> };<data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>.<data-lsp lsp="(property) name: undefined">name</data-lsp> ??=  "taro";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>.<data-lsp lsp="(property) name: undefined">name</data-lsp>);taroconst  <data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "kaori" };<data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp> ??=  "taro";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>);kaori`
```

```
js`const  <data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>  = { <data-lsp lsp="(property) name: undefined">name</data-lsp>:  <data-lsp lsp="var undefined">undefined</data-lsp> };<data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>.<data-lsp lsp="(property) name: undefined">name</data-lsp> ??=  "taro";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user1: {
    name: undefined;
}">user1</data-lsp>.<data-lsp lsp="(property) name: undefined">name</data-lsp>);taroconst  <data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "kaori" };<data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp> ??=  "taro";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const user2: {
    name: string;
}">user2</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>);kaori`
```

### `@` 装饰器（decorator） ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

装饰器用于为类或类成员添加注释，并且是使用装饰器的标志符号。

### `` 数组文字（array literal notation） ![js​

用于数组文字的开始，例如`[1, 2, 3]`。

### `` 访问器（bracket notation） ![js​

用于访问数组元素或对象属性的符号。

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];<data-lsp lsp="const numbers: number[]">numbers</data-lsp>[0];1const  <data-lsp lsp="const object: {
    a: number;
    b: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2 };<data-lsp lsp="const object: {
    a: number;
    b: number;
}">object</data-lsp>["a"];1`
```

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];<data-lsp lsp="const numbers: number[]">numbers</data-lsp>[0];1const  <data-lsp lsp="const object: {
    a: number;
    b: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2 };<data-lsp lsp="const object: {
    a: number;
    b: number;
}">object</data-lsp>["a"];1`
```

### `` 数组的解构赋值（destructuring assignment） ![js​

用于可迭代对象的解构赋值的起始符号。

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const [<data-lsp lsp="const first: number">first</data-lsp>,  ...<data-lsp lsp="const rest: number[]">rest</data-lsp>] = <data-lsp lsp="const numbers: number[]">numbers</data-lsp>;// 分割代入<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const first: number">first</data-lsp>, <data-lsp lsp="const rest: number[]">rest</data-lsp>);1 [ 2, 3 ]// 分割代入 function  <data-lsp lsp="function func([first, ...rest]: [any, ...any[]]): void">func</data-lsp>([<data-lsp lsp="(parameter) first: any">first</data-lsp>,  ...<data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>]) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) first: any">first</data-lsp>, <data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>);}<data-lsp lsp="function func([first, ...rest]: [any, ...any[]]): void">func</data-lsp>([1,  2,  3]);1 [ 2, 3 ]`
```

```
js`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];const [<data-lsp lsp="const first: number">first</data-lsp>,  ...<data-lsp lsp="const rest: number[]">rest</data-lsp>] = <data-lsp lsp="const numbers: number[]">numbers</data-lsp>;// 分割代入<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const first: number">first</data-lsp>, <data-lsp lsp="const rest: number[]">rest</data-lsp>);1 [ 2, 3 ]// 分割代入 function <data-lsp lsp="function func([first, ...rest]: [any, ...any[]]): void">func</data-lsp>([<data-lsp lsp="(parameter) first: any">first</data-lsp>,  ...<data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>]) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) first: any">first</data-lsp>, <data-lsp lsp="(parameter) rest: any[]">rest</data-lsp>);}<data-lsp lsp="function func([first, ...rest]: [any, ...any[]]): void">func</data-lsp>([1,  2,  3]);1 [ 2, 3 ]`
```

### `` 索引类型（index signature） ![ts​

用于索引类型(index signature)的开始符号。

```
ts`type  <data-lsp lsp="type StringKeysAndStringValues = {
    [key: string]: string;
}">StringKeysAndStringValues</data-lsp>  = { [<data-lsp lsp="(parameter) key: string">key</data-lsp>:  string]:  string;};`
```

```
ts`type <data-lsp lsp="type StringKeysAndStringValues = {
    [key: string]: string;
}">StringKeysAndStringValues</data-lsp> = { [<data-lsp lsp="(parameter) key: string">key</data-lsp>:  string]:  string;};`
```

[## 📄️ 索引类型

在 TypeScript 中，有时您可能希望不指定对象的字段名称，而只指定属性。这时，索引类型(index signature)就派上用场了。例如，下面这样注释所有属性都是数字类型的对象。

### `[]` 数组类型（array type） ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

用于表示数组类型的符号。

```
ts`let <data-lsp lsp="let names: string[]">names</data-lsp>:  string[];type  <data-lsp lsp="type FooList = Foo[]">FooList</data-lsp>  =  <data-lsp lsp="class Foo">Foo</data-lsp>[];`
```

```
ts`let <data-lsp lsp="let names: string[]">names</data-lsp>:  string[];type <data-lsp lsp="type FooList = Foo[]">FooList</data-lsp> = <data-lsp lsp="class Foo">Foo</data-lsp>[];`
```

### `\` 字符串转义字符（escaping character） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

用于字符串转义序列的起始符号。

```
js`const  <data-lsp lsp="const lineBreak: &quot;\n&quot;">lineBreak</data-lsp>  =  "\n";`
```

```
js`const  <data-lsp lsp="const lineBreak: &quot;\n&quot;">lineBreak</data-lsp>  =  "\n";`
```

### `^` 位异或（bitwise xor） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

将左值和右值的位值不同的位设置为 1。

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> ^ <data-lsp lsp="const b: 5">b</data-lsp>);00000100// 出力: 4`
```

```
js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001const  <data-lsp lsp="const b: 5">b</data-lsp>  =  5;00000101<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 1">a</data-lsp> ^ <data-lsp lsp="const b: 5">b</data-lsp>);00000100// 出力: 4`
```

### `^=` 位异或赋值（bitwise xor assignment） ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左的变量的值和右的值在位的位置上不同的位设置为 1，然后将结果分配给左的变量。

### `_` 数字的分隔符 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

数字的可读性，用作数字的位数分隔符。

```
js`const  <data-lsp lsp="const hyakuman: 1000000">hyakuman</data-lsp>  =  1_000_000;`
```

```
js`const  <data-lsp lsp="const hyakuman: 1000000">hyakuman</data-lsp>  =  1_000_000;`
```

### `_` 下划线变量 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

惯例上，在类似 lodash 的库中可能会用作变量名。如果变量名为`_`，在 JavaScript 中并没有超出变量的特殊含义。

另外，有时会用作不常用变量的接收者。例如，在接收两个参数的回调函数中，如果只使用第二个参数，则有些代码会将第一个参数命名为下划线。

```
js`[1,  2,  3].<data-lsp lsp="(method) Array<number>.map<void>(callbackfn: (value: number, index: number, array: number[]) => void, thisArg?: any): void[]">map</data-lsp>((<data-lsp lsp="(parameter) _: number">_</data-lsp>, <data-lsp lsp="(parameter) index: number">index</data-lsp>) => {  //  _ は 1, 2, 3のような要素値。それを使わないという意味で _ にしている});`
```

```
js`[1,  2,  3].<data-lsp lsp="(method) Array<number>.map<void>(callbackfn: (value: number, index: number, array: number[]) => void, thisArg?: any): void[]">map</data-lsp>((<data-lsp lsp="(parameter) _: number">_</data-lsp>, <data-lsp lsp="(parameter) index: number">index</data-lsp>) => {  //  _ は 1, 2, 3のような要素値。それを使わないという意味で _ にしている});`
```

### ``` テンプレートリテラル (template literal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

テンプレートリテラル(テンプレート文字列)の前後に置かれる記号です。

```

js``字符串文本`;`

```

```

js``字符串文本`;`

```

### `{` ブロック文 (block) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

if 文やfor 文などの構文に付随して使われる記号です。

```

js`if (<data-lsp lsp="let isOK: false">isOK</data-lsp>) {  // ...} else {  // ...}`

```

```

js`if (<data-lsp lsp="let isOK: false">isOK</data-lsp>) {  // ...} else {  // ...}`

```

if 文やfor 文などの構文を伴わないブロック文は、単に変数のスコープを分けることを目的にしていることがあります。

```

js`{  const  <data-lsp lsp="const value: 1">value</data-lsp>  =  1;}{  const  <data-lsp lsp="const value: 2">value</data-lsp>  =  2;  // 使用相同变量名进行初始化，但由于作用域不同，不会出错。}`

```

```

js`{  const  <data-lsp lsp="const value: 1">value</data-lsp>  =  1;}{  const  <data-lsp lsp="const value: 2">value</data-lsp>  =  2;  // 使用相同变量名进行初始化，但由于作用域不同，不会出错。}`

```

### `{` オブジェクトの分割代入 (destructuring assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトの分割代入に用いられる記号です。

```

js`const  <data-lsp lsp="const object: {

    a: 数字;

    b: 数字;

    c: 数字;

    d: 数字;

}">object</data-lsp>  = { <data-lsp lsp="(property) a: 数字">a</data-lsp>:  1, <data-lsp lsp="(property) b: 数字">b</data-lsp>:  2, <data-lsp lsp="(property) c: 数字">c</data-lsp>:  3, <data-lsp lsp="(property) d: 数字">d</data-lsp>:  4 };const { <data-lsp lsp="const a: 数字">a</data-lsp>,  <data-lsp lsp="const b: 数字">b</data-lsp>,  ...<data-lsp lsp="const rest: {

    c: 数字;

    d: 数字;

}">rest</data-lsp> } = <data-lsp lsp="const object: {

    a: 数字;

    b: 数字;

    c: 数字;

    d: 数字;

}">object</data-lsp>; // 分割赋值<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: 任意, ...optionalParams: 任意[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: 数字">a</data-lsp>, <data-lsp lsp="const b: 数字">b</data-lsp>, <data-lsp lsp="const rest: {

    c: 数字;

    d: 数字;

}">rest</data-lsp>);1 2 { c: 3, d: 4 }// 分割赋值 function  <data-lsp lsp="function func({ a, b, ...rest }: {

    [x: 字符串]: 任意;

    a: 任意;

    b: 任意;

}): void">func</data-lsp>({ <data-lsp lsp="(parameter) a: 任意">a</data-lsp>, <data-lsp lsp="(parameter) b: 任意">b</data-lsp>,  ...<data-lsp lsp="(parameter) rest: {

    [x: 字符串]: 任意;

}">rest</data-lsp> }) {  <data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: 任意, ...optionalParams: 任意[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) a: 任意">a</data-lsp>, <data-lsp lsp="(parameter) b: 任意">b</data-lsp>, <data-lsp lsp="(parameter) rest: {

    [x: 字符串]: 任意;

}">rest</data-lsp>);}<data-lsp lsp="function func({ a, b, ...rest }: {

    [x: 字符串]: 任意;

    a: 任意;

    b: 任意;

}): void">func</data-lsp>(<data-lsp lsp="const object: {

    a: 数字;

    b: 数字;

    c: 数字;

    d: 数字;

}">object</data-lsp>);1 2 { c: 3, d: 4 }`

```

```

js`const  <data-lsp lsp="const object: {

    a: 数字;

    b: 数字;

    c: 数字;

    d: 数字;

}">object</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3, <data-lsp lsp="(property) d: number">d</data-lsp>:  4 };const { <data-lsp lsp="const a: number">a</data-lsp>,  <data-lsp lsp="const b: number">b</data-lsp>,  ...<data-lsp lsp="const rest: {

    c: number;

    d: number;

}">rest</data-lsp> } = <data-lsp lsp="const object: {

    a: number;

    b: number;

    c: number;

    d: number;

}">object</data-lsp>; // 分割代入<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: number">a</data-lsp>, <data-lsp lsp="const b: number">b</data-lsp>, <data-lsp lsp="const rest: {

    c: number;

    d: number;

}">rest</data-lsp>);1 2 { c: 3, d: 4 }// 分割代入 function <data-lsp lsp="function func({ a, b, ...rest }: {

    [x: string]: any;

    a: any;

    b: any;

}): void">func</data-lsp>({ <data-lsp lsp="(parameter) a: any">a</data-lsp>, <data-lsp lsp="(parameter) b: any">b</data-lsp>,  ...<data-lsp lsp="(parameter) rest: {

    [x: string]: any;

}">rest</data-lsp> }) {  <data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) a: any">a</data-lsp>, <data-lsp lsp="(parameter) b: any">b</data-lsp>, <data-lsp lsp="(parameter) rest: {

    [x: string]: any;

}">rest</data-lsp>);}<data-lsp lsp="function func({ a, b, ...rest }: {

    [x: string]: any;

    a: any;

    b: any;

}): void">func</data-lsp>(<data-lsp lsp="const object: {

    a: number;

    b: number;

    c: number;

    d: number;

}">object</data-lsp>);1 2 { c: 3, d: 4 }`

```

### `|` ビット論理和 (bitwise or) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値と右の値でどちらのビットが1である位置のビットを1にします。

```

js`const  <data-lsp lsp="const a: 2">a</data-lsp>  =  0b010;const  <data-lsp lsp="const b: 5">b</data-lsp>  =  0b101;<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>((<data-lsp lsp="const a: 2">a</data-lsp> | <data-lsp lsp="const b: 5">b</data-lsp>) ===  0b111);true`

```

```

js`const  <data-lsp lsp="const a: 2">a</data-lsp>  =  0b010;const  <data-lsp lsp="const b: 5">b</data-lsp>  =  0b101;<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>((<data-lsp lsp="const a: 2">a</data-lsp> | <data-lsp lsp="const b: 5">b</data-lsp>) ===  0b111);true`

```

### `|` ユニオン型 (union type) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

複数の型を組み合わせたユニオン型を定義します。

```

ts`type  <data-lsp lsp="type ID = string | number">ID</data-lsp>  =  string  |  number;const  <data-lsp lsp="const id1: &quot;e29b41&quot;">id1</data-lsp>  =  "e29b41"; // OKconst  <data-lsp lsp="const id2: 100">id2</data-lsp>  =  100; // OKconst  <data-lsp lsp="const id3: true">id3</data-lsp>  =  true; // ERROR`

```

```

ts`type <data-lsp lsp="type ID = string | number">ID</data-lsp> =  string  |  number;const  <data-lsp lsp="const id1: &quot;e29b41&quot;">id1</data-lsp>  =  "e29b41"; // OKconst  <data-lsp lsp="const id2: 100">id2</data-lsp>  =  100; // OKconst  <data-lsp lsp="const id3: true">id3</data-lsp>  =  true; // ERROR`

```

### `|=` ビット論理和代入 (bitwise or assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数の値と右の値でどちらかがのビットが1である位置のビットを1にした結果を左の変数に割り当てます。

### `||` 論理和 (logical or) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の値がtruthyな場合はそれを返します。そうでないときは右の値を返します。

特にboolean 値の場合は、ひとつでも`true`のときに`true`を返し、そうでない場合に`false`を返します。

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  ||  false);true<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(false  ||  false);false<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(false  ||  "abc");"abc"`

```

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(true  ||  false);true<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(false  ||  false);false<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(false  ||  "abc");"abc"`

```

### `||=` 論理和代入 (logical or assignment) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

左の変数と右の値の`||`論理和の結果を左の変数に割り当てます。

```

js`let <data-lsp lsp="let a: boolean">a</data-lsp> =  false;let <data-lsp lsp="let b: number">b</data-lsp> =  1;<data-lsp lsp="let a: boolean">a</data-lsp> ||= <data-lsp lsp="let b: number">b</data-lsp>;<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: boolean">a</data-lsp>);1`

```

```

js`let <data-lsp lsp="let a: boolean">a</data-lsp> =  false;let <data-lsp lsp="let b: number">b</data-lsp> =  1;<data-lsp lsp="let a: boolean">a</data-lsp> ||= <data-lsp lsp="let b: number">b</data-lsp>;<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let a: boolean">a</data-lsp>);1`

```

### `~` ビット否定演算子 (bitwise not) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

ビットを反転します。

```

js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(~<data-lsp lsp="const a: 1">a</data-lsp>);11111110// 出力: -2`

```

```

js`const  <data-lsp lsp="const a: 1">a</data-lsp>  =  1;00000001<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(~<data-lsp lsp="const a: 1">a</data-lsp>);11111110// 出力: -2`

```

### `~~` Double Tilde ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

ビット否定演算子を2つ重ねたもので、小数点以下を消し去る計算をするイディオムです。JavaScriptにこういう演算子があるわけではなく慣習的なものです。double tildeの計算結果は、正の数については`Math.floor`と同じに、負の数は`Math.ceil`と同じになります。

```

js`~~1.5;1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.floor(x: number): number">floor</data-lsp>(1.5);1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.ceil(x: number): number">ceil</data-lsp>(1.5);2~~-1.5;-1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.floor(x: number): number">floor</data-lsp>(-1.5);-2<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.ceil(x: number): number">ceil</data-lsp>(-1.5);-1`

```

```

js`~~1.5;1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.floor(x: number): number">floor</data-lsp>(1.5);1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.ceil(x: number): number">ceil</data-lsp>(1.5);2~~-1.5;-1<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.floor(x: number): number">floor</data-lsp>(-1.5);-2<data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.ceil(x: number): number">ceil</data-lsp>(-1.5);-1`

```

## キーワード​

### `as` 型アサーション (type assertion) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

TypeScriptコンパイラーが解釈した型を上書きする「型アサーション」に用いられるキーワードです。

### `as const` constアサーション (const assertion) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

変数に含まれるハードコーディングされた値をそのリテラル型で宣言し、読み取り専用にします。

```

ts`let <data-lsp lsp="let hello: string" style="border-bottom:solid 2px lightgrey">hello</data-lsp> =  "hello";` `let hello: stringlet <data-lsp lsp="let bye: &quot;bye&quot;" style="border-bottom:solid 2px lightgrey">bye</data-lsp> =  "bye"  as  <data-lsp lsp="type const = &quot;bye&quot;">const</data-lsp>;` `let bye: "bye"const  <data-lsp lsp="const wolf: {

    caniformia: string;

}" style="border-bottom:solid 2px lightgrey">wolf</data-lsp>  = { <data-lsp lsp="(property) caniformia: string">caniformia</data-lsp>:  "Wolf" };` `const wolf: {

    caniformia: string;

}const  <data-lsp lsp="const fox: {

    readonly caniformia: &quot;Fox&quot;;

}" style="border-bottom:solid 2px lightgrey">fox</data-lsp>  = { <data-lsp lsp="(property) caniformia: &quot;Fox&quot;">caniformia</data-lsp>:  "Fox" } as  <data-lsp lsp="type const = {

    readonly caniformia: &quot;Fox&quot;;

}">const</data-lsp>;` `const fox: {

    readonly caniformia: "Fox";

}`

```
ts`let <data-lsp lsp="let hello: string" style="border-bottom:solid 2px lightgrey">hello</data-lsp> =  "hello";` `let hello: stringlet <data-lsp lsp="let bye: &quot;bye&quot;" style="border-bottom:solid 2px lightgrey">bye</data-lsp> =  "bye"  as  <data-lsp lsp="type const = &quot;bye&quot;">const</data-lsp>;` `let bye: "bye"const  <data-lsp lsp="const wolf: {
    caniformia: string;
}" style="border-bottom:solid 2px lightgrey">wolf</data-lsp>  = { <data-lsp lsp="(property) caniformia: string">caniformia</data-lsp>:  "Wolf" };` `const wolf: {
    caniformia: string;
}const  <data-lsp lsp="const fox: {
    readonly caniformia: &quot;Fox&quot;;
}" style="border-bottom:solid 2px lightgrey">fox</data-lsp>  = { <data-lsp lsp="(property) caniformia: &quot;Fox&quot;">caniformia</data-lsp>:  "Fox" } as  <data-lsp lsp="type const = {
    readonly caniformia: &quot;Fox&quot;;
}">const</data-lsp>;` `const fox: {
    readonly caniformia: "Fox";
}`

### `const` const ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

ブロックスコープを持つ定数定義です。スコープ内では再代入も再宣言もできません。

### `get` ゲッター (get) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトのプロパティが参照されたときに対応する関数が呼ばれます。

```

js`const  <data-lsp lsp="const exam: {

    scores: number[];

    readonly best: number;

}">exam</data-lsp>  = { <data-lsp lsp="(property) scores: number[]">scores</data-lsp>: [50,  70,  90,  80,  100,  60],  get  <data-lsp lsp="(getter) best: number">best</data-lsp>() {  return  <data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.max(...values: number[]): number">max</data-lsp>(...this.<data-lsp lsp="(property) scores: number[]">scores</data-lsp>); },};<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const exam: {

    scores: number[];

    readonly best: number;

}">exam</data-lsp>.<data-lsp lsp="(property) best: number">best</data-lsp>);100`

```

```

js`const  <data-lsp lsp="const exam: {

    scores: number[];

    readonly best: number;

}">exam</data-lsp>  = { <data-lsp lsp="(property) scores: number[]">scores</data-lsp>: [50,  70,  90,  80,  100,  60],  get <data-lsp lsp="(getter) best: number">best</data-lsp>() {  return  <data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.max(...values: number[]): number">max</data-lsp>(...this.<data-lsp lsp="(property) scores: number[]">scores</data-lsp>); },};<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const exam: {

    scores: number[];

    readonly best: number;

}">exam</data-lsp>.<data-lsp lsp="(property) best: number">best</data-lsp>);100`

```

### `in` in 演算子 (in operator) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

プロパティがオブジェクトにある場合に`true`を返す演算子です。

```

js`const  <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "サバイバルTypeScript" };<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("name"  in <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>);true<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("price"  in <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>);false`

```

```

js`const  <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "サバイバルTypeScript" };<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("name"  in <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>);true<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("price"  in <data-lsp lsp="const book: {

    name: string;

}">book</data-lsp>);false`

```

### `in` for-in 構文 ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトの列挙可能プロパティをループするfor-in 構文です。

```

js`const  <data-lsp lsp="const drink: {

    name: string;

    price: number;

}">drink</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "Coffee", <data-lsp lsp="(property) price: number">price</data-lsp>:  500 };for (const  <data-lsp lsp="const property: string">property</data-lsp>  in <data-lsp lsp="const drink: {

    name: string;

    price: number;

}">drink</data-lsp>) {  <data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const property: string">property</data-lsp>);}`

```

```

js`const  <data-lsp lsp="const drink: {

    name: string;

    price: number;

}">drink</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "咖啡", <data-lsp lsp="(property) price: number">price</data-lsp>:  500 };for (const  <data-lsp lsp="const property: string">property</data-lsp>  in <data-lsp lsp="const drink: {

    name: 字符串;

    price: 数字;

}">drink</data-lsp>) {  <data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const property: string">property</data-lsp>);}`

```

### `in` Mapped Types ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

Mapped Typesに現れる`in`です。

```

ts`type  <data-lsp lsp="type MappedType = {

    foo: 字符串;

    bar: 字符串;

}">MappedType</data-lsp>  = { [<data-lsp lsp="(type parameter) key">key</data-lsp>  in  "foo"  |  "bar"]:  字符串;};`

```

```

ts`type <data-lsp lsp="type MappedType = {

    foo: 字符串;

    bar: 字符串;

}">MappedType</data-lsp> = { [<data-lsp lsp="(type parameter) key">key</data-lsp> in  "foo"  |  "bar"]:  字符串;};`

```

 ## 📄️ Mapped Types

インデックス型では設定時はどのようなキーも自由に設定できてしまい、アクセス時は毎回 undefinedかどうかの型チェックが必要です。入力の形式が決まっているのであればMapped Typesの使用を検討できます。 

### `is` 型アサーション関数の一部 (user-defined type guard) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

型ガードに用いる型アサーション関数の戻り値の型アノテーション部分に用いられるキーワードです。

```

ts`function  <data-lsp lsp="function isDuck(animal: Animal): animal is Duck">isDuck</data-lsp>(<data-lsp lsp="(parameter) animal: Animal">animal</data-lsp>:  <data-lsp lsp="class Animal">Animal</data-lsp>): <data-lsp lsp="(parameter) animal: Animal">animal</data-lsp> 是  <data-lsp lsp="class Duck">Duck</data-lsp> {  return  <data-lsp lsp="(parameter) animal: Animal">animal</data-lsp>.<data-lsp lsp="(property) Animal.legs: number">legs</data-lsp> ===  2;}`

```

```

ts`function <data-lsp lsp="function isDuck(animal: Animal): animal is Duck">isDuck</data-lsp>(<data-lsp lsp="(parameter) animal: Animal">animal</data-lsp>: <data-lsp lsp="class Animal">Animal</data-lsp>): <data-lsp lsp="(parameter) animal: Animal">animal</data-lsp> 是 <data-lsp lsp="class Duck">Duck</data-lsp> {  return  <data-lsp lsp="(parameter) animal: Animal">animal</data-lsp>.<data-lsp lsp="(property) Animal.legs: number">legs</data-lsp> ===  2;}`

```

### `keyof` keyof 型演算子 (keyof) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

オブジェクトの型からプロパティ名を型として返す型演算子です。

### `n` bigintリテラル (bigint literal) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

数字がbigintリテラルであることを表すのに用いる記号です。

```

js`100n; // bigint 型の100`

```

```

js`100n; // bigint 型の100`

```

### `typeof` typeof 演算子 (typeof) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

与えられた値の型を表す文字列を返します。

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(typeof  123);"number"`

```

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(typeof  123);"number"`

```

### `typeof` typeof 型演算子 (typeof) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

変数から型を抽出する演算子です。

### `set` セッター (set) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

オブジェクトのプロパティを変更するときに対応する関数が呼ばれます。

```

js`const  <data-lsp lsp="module prize

const prize: {

    latest: 字符串;

    history: 从不[];

    winner: 任意;

}">prize</data-lsp>  = { <data-lsp lsp="(property) latest: string">latest</data-lsp>:  "", <data-lsp lsp="(property) history: never[]">history</data-lsp>: [],  set  <data-lsp lsp="(setter) winner: any">winner</data-lsp>(<data-lsp lsp="(parameter) winner: any">winner</data-lsp>) {  this.<data-lsp lsp="(property) latest: string">latest</data-lsp> = <data-lsp lsp="(parameter) winner: any">winner</data-lsp>;  this.<data-lsp lsp="(property) history: never[]">history</data-lsp>.<data-lsp lsp="(method) Array<never>.push(...items: never[]): number">push</data-lsp>(<data-lsp lsp="(parameter) winner: any">winner</data-lsp>); },};<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "斯坦尼斯拉斯·瓦林卡";<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "拉斐尔·纳达尔·帕雷拉";<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "诺瓦克·约科维奇";<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) latest: string">latest</data-lsp>);"诺瓦克·约科维奇"<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) history: never[]">history</data-lsp>);[ '斯坦尼斯拉斯·瓦林卡', '拉斐尔·纳达尔·帕雷拉', '诺瓦克·约科维奇' ]`

```

```

js`const  <data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>  = { <data-lsp lsp="(property) latest: string">latest</data-lsp>:  "", <data-lsp lsp="(property) history: never[]">history</data-lsp>: [],  set <data-lsp lsp="(setter) winner: any">winner</data-lsp>(<data-lsp lsp="(parameter) winner: any">winner</data-lsp>) {  this.<data-lsp lsp="(property) latest: string">latest</data-lsp> = <data-lsp lsp="(parameter) winner: any">winner</data-lsp>;  this.<data-lsp lsp="(property) history: never[]">history</data-lsp>.<data-lsp lsp="(method) Array<never>.push(...items: never[]): number">push</data-lsp>(<data-lsp lsp="(parameter) winner: any">winner</data-lsp>); },};<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "斯坦尼斯拉斯·瓦林卡";<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "Rafael Nadal Parera";<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) winner: any">winner</data-lsp> =  "Novak Đoković";<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) latest: string">latest</data-lsp>);"Novak Đoković"<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="module prize

const prize: {

    latest: string;

    history: never[];

    winner: any;

}">prize</data-lsp>.<data-lsp lsp="(property) history: never[]">history</data-lsp>);[ 'Stanislas Wawrinka', 'Rafael Nadal Parera', 'Novak Đoković' ]`

```

### `void` void 演算子 (void) ![js](img/f2bff360fa9c865072b1586c301e7b00.png)​

戻り値を`undefined`にします。

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(void  123);undefined`

```

```

js`<data-lsp lsp="namespace console

var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(void  123);undefined`

```

### `void` void 型 (void) ![ts](img/e72a734a64b7040e4ddce8739b9f891f.png)​

戻り値が`undefined`あるいはない場合に使用します。

```

ts`function  <data-lsp lsp="function returnUndefined(num: number): void">returnUndefined</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number):  void {  if (<data-lsp lsp="(parameter) num: number">num</data-lsp> ===  0) {  return  <data-lsp lsp="var undefined">undefined</data-lsp>; }  return;}`

```

```

ts`function <data-lsp lsp="function returnUndefined(num: number): void">returnUndefined</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number):  void {  if (<data-lsp lsp="(parameter) num: number">num</data-lsp> ===  0) {  return  <data-lsp lsp="var undefined">undefined</data-lsp>; }  return;}`

```

 ## 📄️ 戻り値がない関数とvoid 型

TypeScriptで戻り値がない関数の戻り値を型注釈するにはvoid 型を用います。void 型は関数の戻り値を型注釈するためにある特別な型です。    

```

```
