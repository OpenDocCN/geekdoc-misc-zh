# TypeScript

> 原文：[`typescriptbook.jp/`](https://typescriptbook.jp/)

注記

本書『サバイバルTypeScript』は実務でTypeScriptを使う開発者のための入門書です。そして、このページはTypeScriptの特徴を最速で把握できるよう、数百ページからなる本書のコンテンツをつまみ食いした要約です。

» 本書ついて詳しく知る

» とにかく今すぐTypeScriptを書いてみたい

## TypeScriptとは​

+   JavaScriptの**スーパーセット**となるプログラミング言語。

+   **静的型付け言語**であり、プログラムの正しさが**静的に検査**できる。

+   ライブラリやIDEなどの開発環境が充実しており、**大きなエコシステム**を持っている。

+   **Microsoft**が2012 年に開発し、**オープンソース**で公開した。

» TypeScriptの特徴について詳しく知る

» TypeScript 誕生の背景について詳しく知る

## TypeScriptはJavaScriptのスーパーセット​

+   **スーパーセット**とは、元の言語との**互換性**を保ちつつ、元の言語を**拡張**して作った言語のこと。

+   TypeScriptは、JavaScriptとの互換性を保ちつつ、JavaScriptを拡張して作った言語である。

+   よって、JavaScriptのコードはすべてTypeScriptとしてあつかえる。

+   TypeScriptは、型注釈やインターフェース、ジェネリクスなど独自の機能を追加している。

TypeScriptの機能とJavaScriptの機能

![](img/f21208fd99a2705a1642c04b474fed54.png)

### スーパーセットのメリット​

+   **学習のしやすさ**: JavaScriptの知識を活かしてTypeScriptを学べる。

+   **資産が活かせる**: 既存のJavaScriptコード資産を活かして開発できる。

+   **移行のしやすさ**: 既存のJavaScriptプロジェクトはTypeScriptへ移行がしやすい。

» TypeScriptとJavaScriptの関係について詳しく知る

## 静的な検査​

+   TypeScriptはプログラムの正しさを静的に検査できる。

+   JavaScriptは実行しないとバグがあるかを確かめられない。

+   TypeScriptは実行せずにチェックが行える。

» 静的な検査について詳しく知��

### 開発効率と品質を向上し、安心感を高める​

+   問題を早期に発見し、開発を効率化できる。

+   コーディング時に問題を発見し、修正できるため、バグを予防できる。

+   エディターとTypeScriptを連携させると、リアルタイムのチェックやコード補完が可能。

エディター上でのフィードバック

![](img/e8222f986033e999ae7b07a1ae5ec855.png)

+   問題を早期に修正できることで、製品の信頼感や安心感が高まる。

+   見通しの悪い大規模なプログラムや、重要なシステムの開発では静的な検査が安心材料になる。

## 検査の仕組み​

+   TypeScriptの検査は**型システム**に基づく。

+   型システムに基づき、**コンパイル**のタイミングでプログラムを検査する。

### 型システム​

+   型システムは、データの種別ごとに型を与え、データに対して行える操作に制約を設ける。

+   これにより、変数には決められた値のみが代入され、決められた操作のみが行われることが保証され、プログラムが正確で安全になる。

+   型システムは、数学の「型理論」を背景に構築され、数学的証明によりプログラムの欠陥をあぶり出せる。

### 型注釈​

+   変数にどのような値が代入できるのかを制約するものを「**型**」と言う。

+   開発者は、変数がどのような型なのかを**型注釈**で指定する。

+   TypeScriptでは、型注釈を手がかりに検査が行われる。

型注釈

![](img/a31ec519278231ed0ee3aa8e2902849f.png)

### 型推論​

+   値の型が文脈で明白な場合、型が自動で判断される。この仕組みを**型推論**という。

+   型推論のおかげで、開発者は型注釈を割愛でき、記述量を減らせる。

型推論

![](img/1a688505f95f7034fdcc074fd3aa103f.png)

### コンパイル​

+   TypeScriptを実行するために、JavaScriptへ変換する。この変換のことを**コンパイル**という。

+   変換後のJavaScriptコードはブラウザやサーバーで実行できる。

+   TypeScriptの検査はコンパイルのタイミングで行われる。

コンパイル

![](img/55bec6342572c2b22cc5f299c2a57062.png)

## 型はドキュメント、リファクタリング、ツールの充実にも寄与​

+   **ドキュメントになる**: 型情報はドキュメントの役割を果たし、コードの理解を助ける。

+   **リファクタリングが安全に**: 変数の型や関数のシグネチャを変更したとき、修正が必要な箇所がコンパイル時にすべて分かり、不注意による誤修正を減らせる。

+   **ツールサポートが充実**: IDEやエディターでのリアルタイムのエラーチェック、自動補完、リファクタリングツール、ナビゲーションなど、開発ツールのサポートが充実している。

» TypeScriptを使う動機について詳しく知る

## 多くのエディターがTypeScriptをサポート​

+   Visual Studio Code

+   JetBrains IDE (IntelliJ, WebStorm, PhpStorm, RubyMine, PyCharm, GoLandなど)

+   Vim

+   NeoVim

+   Emacs (Tide)

+   原子

+   Sublime Text

» TypeScriptとエコシステムについて詳しく知る

## 多様なソフトウェアが作れる​

作れるものの範囲が広いことは、TypeScriptの魅力のひとつ。

+   **Webアプリケーション**: TypeScriptの主戦場。フロントエンドの開発に広く使用される。

+   **サーバーサイドアプリケーション**: Node.jsと組み合わせて、バックエンドやAPIサーバーを開発することが可能。

+   **モバイルアプリケーション**: React Nativeなどのフレームワークを利用して、モバイルアプリケーションを開発できる。

+   **デスクトップアプリケーション**: Electronを使用して、クロスプラットフォームのデスクトップアプリを開発できる。

+   **クラウド関連の機能**: AWS LambdaやAzure Functionsなどのクラウドプラットフォームで、サーバーレス関数が作成できる。

+   **ユーティリティーやCLIツール**: コマンドラインツールや各種ユーティリティの開発ができる。

+   **インフラ構成管理(IaC)**: PulumiやAWS CDKを使用して、インフラの構成を管理することができる。

+   **アプリケーションの拡張機能**: Google ChromeやVisual Studio Codeなどデスクトップアプリケーションの拡張をTypeScriptで開発できる。

» TypeScriptの射程圏について詳しく知る

## TypeScriptを導入した企業の感想​

+   **[Slack](https://slack.engineering/typescript-at-slack/)**: コードベースが大規模になっても、型システムが安全性と信頼性を保証してくれる。

+   **[Airbnb](https://www.reddit.com/r/typescript/comments/aofcik/38_of_bugs_at_airbnb_could_have_been_prevented_by/)**: TypeScriptを使っていたらAirbnbの38%ものバグを未然に防げた。

+   **[ヤフー株式会社](https://codezine.jp/article/detail/16905)**: 静的型付けによりコードの品質とメンテナンス性が向上し、IDEとの連携により開発者の生産性が向上した。

+   **[LINE 株式会社](https://logmi.jp/tech/articles/322702)**: ちょっとした修正でもかかるQAのコストを、TypeScript 化によって抑制。

+   **[Sansan 株式会社](https://buildersbox.corp-sansan.com/entry/2021/06/24/110000)**: 型がドキュメントとしての役割を果たし、コードリーディングや他チームのコード変更に役立った。採用の文脈でアピールポイントにもなった。

+   **[ラクスル株式会社](https://techblog.raksul.com/entry/2020/10/07/after-introducing-typescript-to-existing-product/)**:型システムの恩恵��得られる、エディターの入力補完を受けられる、コード=ドキュメントという状況を作りやすい。

## 基本的な型​

### プリミティブ型​

+   `boolean`: 真偽値。

+   `number`: 数値。

+   `string`: 文字列。

+   `bigint`: 大きな整数。

+   `symbol`: 一意の値を示す。

+   `undefined`: 値が定義されていない状態を示す。

+   `null`: 値が存在しない状態を示す。

```
typescript`const  <data-lsp lsp="const isReady: boolean">isReady</data-lsp>:  boolean  =  false;const  <data-lsp lsp="const age: number">age</data-lsp>:  number  =  25;const  <data-lsp lsp="const fullName: string">fullName</data-lsp>:  string  =  "John Doe";const  <data-lsp lsp="const bigNumber: bigint">bigNumber</data-lsp>:  bigint  =  100n;const  <data-lsp lsp="const uniqueSymbol: symbol">uniqueSymbol</data-lsp>:  symbol  =  <data-lsp lsp="var Symbol: SymbolConstructor
(description?: string | number | undefined) => symbol">Symbol</data-lsp>("unique");const  <data-lsp lsp="const notDefined: undefined">notDefined</data-lsp>:  undefined  =  <data-lsp lsp="var undefined">undefined</data-lsp>;const  <data-lsp lsp="const empty: null">empty</data-lsp>:  null  =  null;`
```

```
typescript`const  <data-lsp lsp="const isReady: boolean">isReady</data-lsp>:  boolean  =  false;const  <data-lsp lsp="const age: number">age</data-lsp>:  number  =  25;const  <data-lsp lsp="const fullName: string">fullName</data-lsp>:  string  =  "John Doe";const  <data-lsp lsp="const bigNumber: bigint">bigNumber</data-lsp>:  bigint  =  100n;const  <data-lsp lsp="const uniqueSymbol: symbol">uniqueSymbol</data-lsp>:  symbol  =  <data-lsp lsp="var Symbol: SymbolConstructor
(description?: string | number | undefined) => symbol">Symbol</data-lsp>("unique");const  <data-lsp lsp="const notDefined: undefined">notDefined</data-lsp>:  undefined  =  <data-lsp lsp="var undefined">undefined</data-lsp>;const  <data-lsp lsp="const empty: null">empty</data-lsp>:  null  =  null;`
```

### 特殊な型​

+   `any`: 何でも代入できる型。型が不明な場合に使用する。その値に対する操作の制限がなく、型の安全性は弱まる。

+   `unknown`: any 型と似て、何でも代入できる型。その値に対する操作は制限され、型の安全性が保たれる。

+   `void`: 値が存在しないことを示す。関数が何も返さない場合に使用する。

+   `never`: 決して何も返さないことを示す。エラーを投げる関数や無限ループの関数の戻り値として使用する。

```
typescript`const  <data-lsp lsp="const a: any">a</data-lsp>:  any  =  100; // 代入できる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: any">a</data-lsp> *  3); // 操作もできる300const  <data-lsp lsp="const x: unknown">x</data-lsp>:  unknown  =  100; // 代入はできる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-err><data-lsp lsp="const x: unknown">x</data-lsp></data-err> *  3); // 操作はできない'x' is of type 'unknown'.18046'x' is of type 'unknown'.// 戻り値のない関数 function  <data-lsp lsp="function doSomething(): void">doSomething</data-lsp>():  void {}// 戻り値を返すことがありえない関数 function  <data-lsp lsp="function throwError(): never">throwError</data-lsp>():  never {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>();}`
```

```
typescript`const  <data-lsp lsp="const a: any">a</data-lsp>:  any  =  100; // 代入できる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: any">a</data-lsp> *  3); // 操作もできる300const  <data-lsp lsp="const x: unknown">x</data-lsp>:  unknown  =  100; // 代入はできる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-err><data-lsp lsp="const x: unknown">x</data-lsp></data-err> *  3); // 操作はできない'x' is of type 'unknown'.18046'x' is of type 'unknown'.// 戻り値のない関数 function <data-lsp lsp="function doSomething(): void">doSomething</data-lsp>():  void {}// 戻り値を返すことがありえない関数 function <data-lsp lsp="function throwError(): never">throwError</data-lsp>():  never {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>();}`
```

## 型エイリアス​

+   型エイリアスは既存の型を新たな名前で定義する機能。

+   より複雑な型を簡素に表現したり、コードの可読性を向上するのに役立つ。

```
typescript`type  <data-lsp lsp="type StringOrNumber = string | number">StringOrNumber</data-lsp>  =  string  |  number;let <data-lsp lsp="let value: StringOrNumber">value</data-lsp>:  <data-lsp lsp="type StringOrNumber = string | number">StringOrNumber</data-lsp>;<data-lsp lsp="let value: StringOrNumber">value</data-lsp> =  "hello"; // string 型が代入可能<data-lsp lsp="let value: StringOrNumber">value</data-lsp> =  123; // number 型も代入可能`
```

```
typescript`type <data-lsp lsp="type StringOrNumber = string | number">StringOrNumber</data-lsp> =  string  |  number;let <data-lsp lsp="let value: StringOrNumber">value</data-lsp>: <data-lsp lsp="type StringOrNumber = string | number">StringOrNumber</data-lsp>;<data-lsp lsp="let value: StringOrNumber">value</data-lsp> =  "hello"; // string 型が代入可能<data-lsp lsp="let value: StringOrNumber">value</data-lsp> =  123; // number 型も代入可能`
```

## 構造的部分型​

+   TypeScriptは構造的部分型を採用している。

+   構造的部分型では、変数の代入可否を、構造が互換しているかに着目して判定する。

```
typescript`type  <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string };type  <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };const  <data-lsp lsp="const johnDetail: Detail">johnDetail</data-lsp>:  <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  28 };const  <data-lsp lsp="const summary: Summary">summary</data-lsp>:  <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp>  = <data-lsp lsp="const johnDetail: Detail">johnDetail</data-lsp>; // 代入できる。構造的部分型として互換があるためconst  <data-lsp lsp="const johnSummary: Summary">johnSummary</data-lsp>:  <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John" };const  <data-err><data-lsp lsp="const detail: Detail">detail</data-lsp></data-err>:  <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp>  = <data-lsp lsp="const johnSummary: Summary">johnSummary</data-lsp>; // 代入できない。構造的部分型として互換がない（ageを含まないため）Property 'age' is missing in type 'Summary' but required in type 'Detail'.2741Property 'age' is missing in type 'Summary' but required in type 'Detail'.`
```

```
typescript`type <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string };type <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };const  <data-lsp lsp="const johnDetail: Detail">johnDetail</data-lsp>: <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  28 };const  <data-lsp lsp="const summary: Summary">summary</data-lsp>: <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp> = <data-lsp lsp="const johnDetail: Detail">johnDetail</data-lsp>; // 代入できる。構造的部分型として互換があるためconst  <data-lsp lsp="const johnSummary: Summary">johnSummary</data-lsp>: <data-lsp lsp="type Summary = {
    name: string;
}">Summary</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John" };const  <data-err><data-lsp lsp="const detail: Detail">detail</data-lsp></data-err>: <data-lsp lsp="type Detail = {
    name: string;
    age: number;
}">Detail</data-lsp> = <data-lsp lsp="const johnSummary: Summary">johnSummary</data-lsp>; // 代入できない。構造的部分型として互換がない（ageを含まないため）Property 'age' is missing in type 'Summary' but required in type 'Detail'.2741Property 'age' is missing in type 'Summary' but required in type 'Detail'.`
```

## 配列​

### 配列リテラル​

+   配列の値を作るには配列リテラル(`[]`)を使う。

+   `[要素 1, 要素 2, ...]`の形で配列の初期値を設定できる。

```
typescript`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];`
```

```
typescript`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];`
```

### 配列の型注釈​

+   配列の型注釈には`型名[]`または`Array<型名>`を使う。

```
typescript`let <data-lsp lsp="let numbers: number[]">numbers</data-lsp>:  number[];let <data-lsp lsp="let strings: string[]">strings</data-lsp>:  <data-lsp lsp="interface Array<T>">Array</data-lsp><string>;`
```

```
typescript`let <data-lsp lsp="let numbers: number[]">numbers</data-lsp>:  number[];let <data-lsp lsp="let strings: string[]">strings</data-lsp>: <data-lsp lsp="interface Array<T>">Array</data-lsp><string>;`
```

### 配列要素へのアクセス​

+   配列要素にアクセスするにはインデックス（インデックス）を使う。

+   0から始まる整数を指定して配列の値を取得し、代入も可能。

```
typescript`const  <data-lsp lsp="const colors: string[]">colors</data-lsp>  = ["red",  "green",  "blue"];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const colors: string[]">colors</data-lsp>[0]);'red'<data-lsp lsp="const colors: string[]">colors</data-lsp>[1] =  "yellow";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const colors: string[]">colors</data-lsp>);['red', 'yellow', 'blue']`
```

```
typescript`const  <data-lsp lsp="const colors: string[]">colors</data-lsp>  = ["red",  "green",  "blue"];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const colors: string[]">colors</data-lsp>[0]);'red'<data-lsp lsp="const colors: string[]">colors</data-lsp>[1] =  "yellow";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const colors: string[]">colors</data-lsp>);['red', 'yellow', 'blue']`
```

### 読み取り専用配列​

+   読み取り専用配列は値の変更ができない配列を表す。

+   配列の型注釈に`readonly`をつけると読み取り専用配列となる。

+   `ReadonlyArray<型名>`でも読み取り専用配列が宣言でき、`readonly 型名[]`と機能は同じ。

```
typescript`const  <data-lsp lsp="const numbers: readonly number[]">numbers</data-lsp>:  readonly  number[] = [1,  2,  3];const  <data-lsp lsp="const strings: readonly string[]">strings</data-lsp>:  <data-lsp lsp="interface ReadonlyArray<T>">ReadonlyArray</data-lsp><string> = ["hello",  "world"];<data-lsp lsp="const numbers: readonly number[]">numbers</data-lsp>[0] =  4; // 値を変更できないIndex signature in type 'readonly number[]' only permits reading.2542Index signature in type 'readonly number[]' only permits reading.<data-lsp lsp="const strings: readonly string[]">strings</data-lsp>.<data-err><data-lsp lsp="any">push</data-lsp></data-err>("!"); // 要素を追加できないProperty 'push' does not exist on type 'readonly string[]'.2339Property 'push' does not exist on type 'readonly string[]'.`
```

```
typescript`const  <data-lsp lsp="const numbers: readonly number[]">numbers</data-lsp>:  readonly  number[] = [1,  2,  3];const  <data-lsp lsp="const strings: readonly string[]">strings</data-lsp>: <data-lsp lsp="interface ReadonlyArray<T>">ReadonlyArray</data-lsp><string> = ["hello",  "world"];<data-lsp lsp="const numbers: readonly number[]">numbers</data-lsp>[0] =  4; // 値を変更できないIndex signature in type 'readonly number[]' only permits reading.2542Index signature in type 'readonly number[]' only permits reading.<data-lsp lsp="const strings: readonly string[]">strings</data-lsp>.<data-err><data-lsp lsp="any">push</data-lsp></data-err>("!"); // 要素を追加できないProperty 'push' does not exist on type 'readonly string[]'.2339Property 'push' does not exist on type 'readonly string[]'.`
```

### 配列のループ​

+   配列をループするための`for...of`構文もある。

```
typescript`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];for (const  <data-lsp lsp="const num: number">num</data-lsp>  of <data-lsp lsp="const numbers: number[]">numbers</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const num: number">num</data-lsp>); // 1, 2, 3と出力される}`
```

```
typescript`const  <data-lsp lsp="const numbers: number[]">numbers</data-lsp>  = [1,  2,  3];for (const  <data-lsp lsp="const num: number">num</data-lsp>  of <data-lsp lsp="const numbers: number[]">numbers</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const num: number">num</data-lsp>); // 1, 2, 3と出力される}`
```

## タプル型​

+   タプル型を使うと、配列の要素数と要素の型が固定される。

+   それぞれの要素のインデックスごとに型が決まる。

```
typescript`let <data-lsp lsp="let tuple: [string, number]">tuple</data-lsp>: [string,  number];<data-lsp lsp="let tuple: [string, number]">tuple</data-lsp> = ["hello",  10]; // 代入できる<data-lsp lsp="let tuple: [string, number]">tuple</data-lsp> = [<data-err>10</data-err>,  <data-err>"hello"</data-err>]; // 順序が正しくないため、代入できないType 'number' is not assignable to type 'string'.
Type 'string' is not assignable to type 'number'.2322
2322Type 'number' is not assignable to type 'string'.
Type 'string' is not assignable to type 'number'.<data-err><data-lsp lsp="let tuple: [string, number]">tuple</data-lsp></data-err> = ["hello",  10,  "world"]; // 要素が多すぎるため代入できないType '[string, number, string]' is not assignable to type '[string, number]'.
  Source has 3 element(s) but target allows only 2.2322Type '[string, number, string]' is not assignable to type '[string, number]'.
  Source has 3 element(s) but target allows only 2.`
```

```
typescript`let <data-lsp lsp="let tuple: [string, number]">tuple</data-lsp>: [string,  number];<data-lsp lsp="let tuple: [string, number]">tuple</data-lsp> = ["hello",  10]; // 代入できる<data-lsp lsp="let tuple: [string, number]">tuple</data-lsp> = [<data-err>10</data-err>,  <data-err>"hello"</data-err>]; // 順序が正しくないため、代入できないType 'number' is not assignable to type 'string'.
Type 'string' is not assignable to type 'number'.2322
2322Type 'number' is not assignable to type 'string'.
Type 'string' is not assignable to type 'number'.<data-err><data-lsp lsp="let tuple: [string, number]">tuple</data-lsp></data-err> = ["hello",  10,  "world"]; // 要素が多すぎるため代入できないType '[string, number, string]' is not assignable to type '[string, number]'.
  Source has 3 element(s) but target allows only 2.2322Type '[string, number, string]' is not assignable to type '[string, number]'.
  Source has 3 element(s) but target allows only 2.`
```

### タプルの要素へのアクセス​

+   タプルの要素にアクセスする場合も配列同様にインデックス（インデックス）を使用する。

```
typescript`const  <data-lsp lsp="const tuple: [string, number]">tuple</data-lsp>: [string,  number] = ["hello",  10];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const tuple: [string, number]">tuple</data-lsp>[0]);'hello'`
```

```
typescript`const  <data-lsp lsp="const tuple: [string, number]">tuple</data-lsp>: [string,  number] = ["hello",  10];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const tuple: [string, number]">tuple</data-lsp>[0]);'hello'`
```

## オブジェクト​

### オブジェクトリテラル​

+   オブジェクトの作り方はオブジェクトリテラル(`{}`)を使う。

+   `{ プロパティキー: 値, ... }` の形でオブジェクトの初期値を設定できる。

```
typescript`const  <data-lsp lsp="const john: {
    name: string;
    age: number;
}">john</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20 };`
```

```
typescript`const  <data-lsp lsp="const john: {
    name: string;
    age: number;
}">john</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20 };`
```

### プロパティアクセス​

+   ドット`.`を使ってオブジェクトのプロパティにアクセスできる。

```
typescript`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: {
    name: string;
    age: number;
}">john</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>);'John'`
```

```
typescript`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: {
    name: string;
    age: number;
}">john</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>);'John'`
```

### オブジェクトの型注釈​

+   オブジェクトの型注釈は`{プロパティ1: ���1, プロパティ2: 型 2, ...}`の形で記述する。

```
typescript`let <data-lsp lsp="let obj: {
    name: string;
    age: number;
}">obj</data-lsp>: { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };`
```

```
typescript`let <data-lsp lsp="let obj: {
    name: string;
    age: number;
}">obj</data-lsp>: { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };`
```

### readonlyプロパティ​

+   `readonly`をつけたプロパティは代入できない。

```
typescript`let <data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp>: { readonly <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };<data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20 };<data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp>.<data-err><data-lsp lsp="(property) name: any">name</data-lsp></data-err> =  "Tom";Cannot assign to 'name' because it is a read-only property.2540Cannot assign to 'name' because it is a read-only property.`
```

```
typescript`let <data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp>: { readonly <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number };<data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20 };<data-lsp lsp="let obj: {
    readonly name: string;
    age: number;
}">obj</data-lsp>.<data-err><data-lsp lsp="(property) name: any">name</data-lsp></data-err> =  "Tom";Cannot assign to 'name' because it is a read-only property.2540Cannot assign to 'name' because it is a read-only property.`
```

### オプションプロパティー​

+   オプショナルプロパティー`?`をつけたプロパティは省略可能。

```
typescript`let <data-lsp lsp="let obj: {
    name: string;
    age?: number | undefined;
}">obj</data-lsp>: { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number };<data-lsp lsp="let obj: {
    name: string;
    age?: number | undefined;
}">obj</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John" }; // `age`プロパティがなくてもエラーにならない`
```

```
typescript`let <data-lsp lsp="let obj: {
    name: string;
    age?: number | undefined;
}">obj</data-lsp>: { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number };<data-lsp lsp="let obj: {
    name: string;
    age?: number | undefined;
}">obj</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John" }; // `age`プロパティがなくてもエラーにならない`
```

### オブジェクトメソッド​

+   関数をプロパティに持つオブジェクトを定義できる。

```
typescript`const  <data-lsp lsp="const obj: {
    a: number;
    b: number;
    sum(): number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2,  <data-lsp lsp="(method) sum(): number">sum</data-lsp>():  number {  return  this.<data-lsp lsp="(property) a: number">a</data-lsp> +  this.<data-lsp lsp="(property) b: number">b</data-lsp>; },};<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const obj: {
    a: number;
    b: number;
    sum(): number;
}">obj</data-lsp>.<data-lsp lsp="(method) sum(): number">sum</data-lsp>());3`
```

```
typescript`const  <data-lsp lsp="const obj: {
    a: number;
    b: number;
    sum(): number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(method) sum(): number">sum</data-lsp>():  number {  return  this.<data-lsp lsp="(property) a: number">a</data-lsp> +  this.<data-lsp lsp="(property) b: number">b</data-lsp>; },};<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const obj: {
    a: number;
    b: number;
    sum(): number;
}">obj</data-lsp>.<data-lsp lsp="(method) sum(): number">sum</data-lsp>());3`
```

### インデックス型​

+   オブジェクトはインデックス型を利用して任意のキーの値を取得することができる。

+   インデックス型プロパティの型注釈は`[キー名: プロパティキーの型]: プロパティ値の型` の形で記述する。

```
typescript`let <data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>: { [<data-lsp lsp="(parameter) key: string">key</data-lsp>:  string]:  number };<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp> = { <data-lsp lsp="(property) key1: number">key1</data-lsp>:  1, <data-lsp lsp="(property) key2: number">key2</data-lsp>:  2 };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>["key1"]);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>["key2"]);2`
```

```
typescript`let <data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>: { [<data-lsp lsp="(parameter) key: string">key</data-lsp>:  string]:  number };<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp> = { <data-lsp lsp="(property) key1: number">key1</data-lsp>:  1, <data-lsp lsp="(property) key2: number">key2</data-lsp>:  2 };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>["key1"]);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let obj: {
    [key: string]: number;
}">obj</data-lsp>["key2"]);2`
```

### Shorthand property names​

+   プロパティの値がすでに定義されている変数である場合、そのプロパティ名を省略して記述できる(shorthand property names)。

```
typescript`const  <data-lsp lsp="const name: &quot;John&quot;">name</data-lsp>  =  "John";const  <data-lsp lsp="const age: 20">age</data-lsp>  =  20;const  <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>, <data-lsp lsp="(property) age: number">age</data-lsp> };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>);{ name: 'John', age: 20 }`
```

```
typescript`const  <data-lsp lsp="const name: &quot;John&quot;">name</data-lsp>  =  "John";const  <data-lsp lsp="const age: 20">age</data-lsp>  =  20;const  <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>, <data-lsp lsp="(property) age: number">age</data-lsp> };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>);{ name: 'John', age: 20 }`
```

### オプショナルチェーン​

+   プロパティが存在するかどうか不確定である場合、`?.`演算子（オプショナルチェーン）で安全にアクセスできる。

```
typescript`function  <data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>(<data-lsp lsp="(parameter) obj: {
    a?: string | undefined;
}">obj</data-lsp>: { <data-lsp lsp="(property) a?: string | undefined">a</data-lsp>?:  string }) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) obj: {
    a?: string | undefined;
}">obj</data-lsp>.<data-lsp lsp="(property) a?: string | undefined">a</data-lsp>?.<data-lsp lsp="(property) String.length: number | undefined">length</data-lsp>);}<data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>({ <data-lsp lsp="(property) a?: string | undefined">a</data-lsp>:  "hello" });5<data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>({});undefined`
```

```
typescript`function <data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>(<data-lsp lsp="(parameter) obj: {
    a?: string | undefined;
}">obj</data-lsp>: { <data-lsp lsp="(property) a?: string | undefined">a</data-lsp>?:  string }) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) obj: {
    a?: string | undefined;
}">obj</data-lsp>.<data-lsp lsp="(property) a?: string | undefined">a</data-lsp>?.<data-lsp lsp="(property) String.length: number | undefined">length</data-lsp>);}<data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>({ <data-lsp lsp="(property) a?: string | undefined">a</data-lsp>:  "hello" });5<data-lsp lsp="function printLength(obj: {
    a?: string;
}): void">printLength</data-lsp>({});undefined`
```

## Map​

### Mapオブジェクト​

+   Mapオブジェクトはキーとそれに対応する値を対にしたコレクション。

+   キーはオブジェクトも含め任意の値が可能。

```
typescript`const  <data-lsp lsp="const map: Map<any, any>">map</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new () => Map<any, any> (+3 overloads)">Map</data-lsp>();<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.set(key: any, value: any): Map<any, any>">set</data-lsp>("name",  "John");<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.set(key: any, value: any): Map<any, any>">set</data-lsp>("age",  "20");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.get(key: any): any">get</data-lsp>("name"));'John'`
```

```
typescript`const  <data-lsp lsp="const map: Map<any, any>">map</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new () => Map<any, any> (+3 overloads)">Map</data-lsp>();<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.set(key: any, value: any): Map<any, any>">set</data-lsp>("name",  "John");<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.set(key: any, value: any): Map<any, any>">set</data-lsp>("age",  "20");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map: Map<any, any>">map</data-lsp>.<data-lsp lsp="(method) Map<any, any>.get(key: any): any">get</data-lsp>("name"));'John'`
```

### Mapの型注釈​

+   Mapの型注釈は`Map<キーの型, 値の型>`の形で記述する。

```
typescript`let <data-lsp lsp="let people: Map<string, number>">people</data-lsp>:  <data-lsp lsp="interface Map<K, V>">Map</data-lsp><string,  number>;`
```

```
typescript`let <data-lsp lsp="let people: Map<string, number>">people</data-lsp>: <data-lsp lsp="interface Map<K, V>">Map</data-lsp><string,  number>;`
```

### Mapのループ​

+   Mapオブジェクトは`for...of`でループすると、各エントリーがキーと値の配列として順に取得できる。

+   要素の順序は、要素を追加した順が保証されている。

```
typescript`for (const [<data-lsp lsp="const key: string">key</data-lsp>,  <data-lsp lsp="const value: number">value</data-lsp>] of <data-lsp lsp="const map: Map<string, number>">map</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const key: string">key</data-lsp>, <data-lsp lsp="const value: number">value</data-lsp>);}`
```

```
typescript`for (const [<data-lsp lsp="const key: string">key</data-lsp>,  <data-lsp lsp="const value: number">value</data-lsp>] of <data-lsp lsp="const map: Map<string, number>">map</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const key: string">key</data-lsp>, <data-lsp lsp="const value: number">value</data-lsp>);}`
```

## Set​

### Set オブジェクト​

+   Setオブジェクトは同じ値が存在しないコレクション。

+   Setの要素は何でも可能である。

```
typescript`const  <data-lsp lsp="const set: Set<unknown>">set</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <unknown>(iterable?: Iterable<unknown> | null | undefined) => Set<unknown> (+1 overload)">Set</data-lsp>();<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(1);<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(2);<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(2); // 同じ値は追加されない。<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set: Set<unknown>">set</data-lsp>);Set {1, 2}`
```

```
typescript`const  <data-lsp lsp="const set: Set<unknown>">set</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <unknown>(iterable?: Iterable<unknown> | null | undefined) => Set<unknown> (+1 overload)">Set</data-lsp>();<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(1);<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(2);<data-lsp lsp="const set: Set<unknown>">set</data-lsp>.<data-lsp lsp="(method) Set<unknown>.add(value: unknown): Set<unknown>">add</data-lsp>(2); // 同じ値は追加されない。<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set: Set<unknown>">set</data-lsp>);Set {1, 2}`
```

### Setの型注釈​

+   Setの型注釈は`Set<要素の型>`の形で記述する。

```
typescript`let <data-lsp lsp="let numSet: Set<number>">numSet</data-lsp>:  <data-lsp lsp="interface Set<T>">Set</data-lsp><number>;`
```

```
typescript`let <data-lsp lsp="let numSet: Set<number>">numSet</data-lsp>: <data-lsp lsp="interface Set<T>">Set</data-lsp><number>;`
```

### Setのループ​

+   SetもMap 同様に`for...of`でループすることが可能。

+   順序は`add`した順。

```
typescript`for (const  <data-lsp lsp="const value: number">value</data-lsp>  of <data-lsp lsp="const set: Set<number>">set</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const value: number">value</data-lsp>);}`
```

```
typescript`for (const  <data-lsp lsp="const value: number">value</data-lsp>  of <data-lsp lsp="const set: Set<number>">set</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const value: number">value</data-lsp>);}`
```

## 列挙型 (Enum)​ への直接リンク")

### 列挙型の基本​

+   列挙型(enum)は、関連する一連の数値または文字列値の集まりを定義する。

+   列挙型は`enum`キーワードを使用して定義する。

```
typescript`enum  <data-lsp lsp="enum Color">Color</data-lsp> { <data-lsp lsp="(enum member) Color.Red = 0">Red</data-lsp>, <data-lsp lsp="(enum member) Color.Green = 1">Green</data-lsp>, <data-lsp lsp="(enum member) Color.Blue = 2">Blue</data-lsp>,}`
```

```
typescript`enum <data-lsp lsp="enum Color">Color</data-lsp> { <data-lsp lsp="(enum member) Color.Red = 0">Red</data-lsp>, <data-lsp lsp="(enum member) Color.Green = 1">Green</data-lsp>, <data-lsp lsp="(enum member) Color.Blue = 2">Blue</data-lsp>,}`
```

### 列挙型に値を設定​

+   列挙体の値は文字列リテラルまたは数値リテラルで指定できる。

```
typescript`enum  <data-lsp lsp="enum Color">Color</data-lsp> { <data-lsp lsp="(enum member) Color.Red = &quot;red&quot;">Red</data-lsp> =  "red", <data-lsp lsp="(enum member) Color.Green = &quot;green&quot;">Green</data-lsp> =  "green", <data-lsp lsp="(enum member) Color.Blue = &quot;blue&quot;">Blue</data-lsp> =  "blue",}`
```

```
typescript`enum <data-lsp lsp="enum Color">Color</data-lsp> { <data-lsp lsp="(enum member) Color.Red = &quot;red&quot;">Red</data-lsp> =  "red", <data-lsp lsp="(enum member) Color.Green = &quot;green&quot;">Green</data-lsp> =  "green", <data-lsp lsp="(enum member) Color.Blue = &quot;blue&quot;">Blue</data-lsp> =  "blue",}`
```

### 列挙型の利用​

+   列挙型の各値にアクセスするにはドット演算子を使用する。

```
typescript`const  <data-lsp lsp="const myColor: Color">myColor</data-lsp>:  <data-lsp lsp="enum Color">Color</data-lsp>  =  <data-lsp lsp="enum Color">Color</data-lsp>.<data-lsp lsp="(enum member) Color.Red = 0">Red</data-lsp>;`
```

```
typescript`const  <data-lsp lsp="const myColor: Color">myColor</data-lsp>: <data-lsp lsp="enum Color">Color</data-lsp> =  <data-lsp lsp="enum Color">Color</data-lsp>.<data-lsp lsp="(enum member) Color.Red = 0">Red</data-lsp>;`
```

## ユニオン型​

+   ユニオン型は複数の型のうちのいずれかをとる値を表現できる。

+   `型 1 | 型 2 | ...`の形式で使う。

+   ひとつ以上の異なる型の値を同じ変数で扱う場合に使用する。

```
typescript`let <data-lsp lsp="let value: number | boolean">value</data-lsp>:  boolean  |  number;<data-lsp lsp="let value: number | boolean">value</data-lsp> =  true; // 代入できる<data-lsp lsp="let value: number | boolean">value</data-lsp> =  100; // 代入できる`
```

```
typescript`let <data-lsp lsp="let value: number | boolean">value</data-lsp>:  boolean  |  number;<data-lsp lsp="let value: number | boolean">value</data-lsp> =  true; // 代入できる<data-lsp lsp="let value: number | boolean">value</data-lsp> =  100; // 代入できる`
```

### 判別可能なユニオン型​

+   判別可能なユニオン型は、共通のリテラル型のプロパティを持つ特別なユニオン型。

+   共通のプロパティを利用して、型を判別できる。

```
typescript`type  <data-lsp lsp="type Triangle = {
    kind: &quot;triangle&quot;;
    base: number;
    height: number;
}">Triangle</data-lsp>  = { <data-lsp lsp="(property) kind: &quot;triangle&quot;">kind</data-lsp>:  "triangle"; <data-lsp lsp="(property) base: number">base</data-lsp>:  number; <data-lsp lsp="(property) height: number">height</data-lsp>:  number };type  <data-lsp lsp="type Rectangle = {
    kind: &quot;rectangle&quot;;
    width: number;
    height: number;
}">Rectangle</data-lsp>  = { <data-lsp lsp="(property) kind: &quot;rectangle&quot;">kind</data-lsp>:  "rectangle"; <data-lsp lsp="(property) width: number">width</data-lsp>:  number; <data-lsp lsp="(property) height: number">height</data-lsp>:  number };type  <data-lsp lsp="type Shape = Triangle | Rectangle">Shape</data-lsp>  =  <data-lsp lsp="type Triangle = {
    kind: &quot;triangle&quot;;
    base: number;
    height: number;
}">Triangle</data-lsp>  |  <data-lsp lsp="type Rectangle = {
    kind: &quot;rectangle&quot;;
    width: number;
    height: number;
}">Rectangle</data-lsp>;function  <data-lsp lsp="function getArea(shape: Shape): number">getArea</data-lsp>(<data-lsp lsp="(parameter) shape: Shape">shape</data-lsp>:  <data-lsp lsp="type Shape = Triangle | Rectangle">Shape</data-lsp>):  number {  // 共通のプロパティkindを利用して型を判定する  switch (<data-lsp lsp="(parameter) shape: Shape">shape</data-lsp>.<data-lsp lsp="(property) kind: &quot;triangle&quot; | &quot;rectangle&quot;">kind</data-lsp>) {  case  "triangle":  // この節ではshapeがTriangle 型に絞り込まれる  return (<data-lsp lsp="(parameter) shape: Triangle">shape</data-lsp>.<data-lsp lsp="(property) base: number">base</data-lsp> *  <data-lsp lsp="(parameter) shape: Triangle">shape</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>) /  2;  case  "rectangle":  //  この節ではshapeがRectangle 型に絞り込まれる  return  <data-lsp lsp="(parameter) shape: Rectangle">shape</data-lsp>.<data-lsp lsp="(property) width: number">width</data-lsp> *  <data-lsp lsp="(parameter) shape: Rectangle">shape</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>; }}`
```

```
typescript`type <data-lsp lsp="type Triangle = {
    kind: &quot;triangle&quot;;
    base: number;
    height: number;
}">Triangle</data-lsp> = { <data-lsp lsp="(property) kind: &quot;triangle&quot;">kind</data-lsp>:  "triangle"; <data-lsp lsp="(property) base: number">base</data-lsp>:  number; <data-lsp lsp="(property) height: number">height</data-lsp>:  number };type <data-lsp lsp="type Rectangle = {
    kind: &quot;rectangle&quot;;
    width: number;
    height: number;
}">Rectangle</data-lsp> = { <data-lsp lsp="(property) kind: &quot;rectangle&quot;">kind</data-lsp>:  "rectangle"; <data-lsp lsp="(property) width: number">width</data-lsp>:  number; <data-lsp lsp="(property) height: number">height</data-lsp>:  number };type <data-lsp lsp="type Shape = Triangle | Rectangle">Shape</data-lsp> = <data-lsp lsp="type Triangle = {
    kind: &quot;triangle&quot;;
    base: number;
    height: number;
}">Triangle</data-lsp> | <data-lsp lsp="type Rectangle = {
    kind: &quot;rectangle&quot;;
    width: number;
    height: number;
}">Rectangle</data-lsp>;function <data-lsp lsp="function getArea(shape: Shape): number">getArea</data-lsp>(<data-lsp lsp="(parameter) shape: Shape">shape</data-lsp>: <data-lsp lsp="type Shape = Triangle | Rectangle">Shape</data-lsp>):  number {  // 共通のプロパティkindを利用して型を判定する  switch (<data-lsp lsp="(parameter) shape: Shape">shape</data-lsp>.<data-lsp lsp="(property) kind: &quot;triangle&quot; | &quot;rectangle&quot;">kind</data-lsp>) {  case  "triangle":  // この節ではshapeがTriangle 型に絞り込まれる  return (<data-lsp lsp="(parameter) shape: Triangle">shape</data-lsp>.<data-lsp lsp="(property) base: number">base</data-lsp> *  <data-lsp lsp="(parameter) shape: Triangle">shape</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>) /  2;  case  "rectangle":  //  この節ではshapeがRectangle 型に絞り込まれる  return  <data-lsp lsp="(parameter) shape: Rectangle">shape</data-lsp>.<data-lsp lsp="(property) width: number">width</data-lsp> *  <data-lsp lsp="(parameter) shape: Rectangle">shape</data-lsp>.<data-lsp lsp="(property) height: number">height</data-lsp>; }}`
```

## インターセクション型​

+   インターセクション型は複数の型を1つに結合した新しい型を定義する。

+   `型 1 & 型 2 & ...`の形式で使う。

+   その結果として生じた型は、それぞれの型が持つすべてのプロパティとメソッドを備えている。

```
typescript`type  <data-lsp lsp="type Octopus = {
    swims: boolean;
}">Octopus</data-lsp>  = { <data-lsp lsp="(property) swims: boolean">swims</data-lsp>:  boolean };type  <data-lsp lsp="type Cat = {
    nightVision: boolean;
}">Cat</data-lsp>  = { <data-lsp lsp="(property) nightVision: boolean">nightVision</data-lsp>:  boolean };type  <data-lsp lsp="type Octocat = Octopus &amp; Cat">Octocat</data-lsp>  =  <data-lsp lsp="type Octopus = {
    swims: boolean;
}">Octopus</data-lsp>  &  <data-lsp lsp="type Cat = {
    nightVision: boolean;
}">Cat</data-lsp>;const  <data-lsp lsp="const octocat: Octocat">octocat</data-lsp>:  <data-lsp lsp="type Octocat = Octopus &amp; Cat">Octocat</data-lsp>  = { <data-lsp lsp="(property) swims: boolean">swims</data-lsp>:  true, <data-lsp lsp="(property) nightVision: boolean">nightVision</data-lsp>:  true };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const octocat: Octocat">octocat</data-lsp>);{ swims: true, nightVision: true }`
```

```
typescript`type <data-lsp lsp="type Octopus = {
    swims: boolean;
}">Octopus</data-lsp> = { <data-lsp lsp="(property) swims: boolean">swims</data-lsp>:  boolean };type <data-lsp lsp="type Cat = {
    nightVision: boolean;
}">Cat</data-lsp> = { <data-lsp lsp="(property) nightVision: boolean">nightVision</data-lsp>:  boolean };type <data-lsp lsp="type Octocat = Octopus &amp; Cat">Octocat</data-lsp> = <data-lsp lsp="type Octopus = {
    swims: boolean;
}">Octopus</data-lsp> & <data-lsp lsp="type Cat = {
    nightVision: boolean;
}">Cat</data-lsp>;const  <data-lsp lsp="const octocat: Octocat">octocat</data-lsp>: <data-lsp lsp="type Octocat = Octopus &amp; Cat">Octocat</data-lsp> = { <data-lsp lsp="(property) swims: boolean">swims</data-lsp>:  true, <data-lsp lsp="(property) nightVision: boolean">nightVision</data-lsp>:  true };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const octocat: Octocat">octocat</data-lsp>);{ swims: true, nightVision: true }`
```

## 分割代入​

+   分割代入を使うと、配列の各要素を一度に変数に代入できる(配列の分割代入)。

```
typescript`const [<data-lsp lsp="const a: number">a</data-lsp>,  <data-lsp lsp="const b: number">b</data-lsp>] = [1,  2];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: number">a</data-lsp>);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const b: number">b</data-lsp>);2`
```

```
typescript`const [<data-lsp lsp="const a: number">a</data-lsp>,  <data-lsp lsp="const b: number">b</data-lsp>] = [1,  2];<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const a: number">a</data-lsp>);1<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const b: number">b</data-lsp>);2`
```

+   分割代入により、オブジェクトのプロパティを個別の変数へ代入できる(オブジェクトの分割代入)。

```
typescript`const  <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20,};const { <data-lsp lsp="const name: string">name</data-lsp>,  <data-lsp lsp="const age: number">age</data-lsp> } = <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const name: string">name</data-lsp>);'John'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const age: number">age</data-lsp>);20`
```

```
typescript`const  <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "John", <data-lsp lsp="(property) age: number">age</data-lsp>:  20,};const { <data-lsp lsp="const name: string">name</data-lsp>,  <data-lsp lsp="const age: number">age</data-lsp> } = <data-lsp lsp="const obj: {
    name: string;
    age: number;
}">obj</data-lsp>;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const name: string">name</data-lsp>);'John'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const age: number">age</data-lsp>);20`
```

## 条件分岐​

+   TypeScriptではJavaScriptと同様に、条件分岐には`if`構文や`switch`構文が利用できる。

### if-else 文​

```
typescript`const  <data-lsp lsp="const age: number">age</data-lsp>:  number  =  20;if (<data-lsp lsp="const age: number">age</data-lsp> >=  20) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("You are an adult.");} else {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("You are a minor.");}'You are an adult.'`
```

```
typescript`const  <data-lsp lsp="const age: number">age</data-lsp>:  number  =  20;if (<data-lsp lsp="const age: number">age</data-lsp> >=  20) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("You are an adult.");} else {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("You are a minor.");}'You are an adult.'`
```

### switch 文​

```
typescript`const  <data-lsp lsp="const color: string">color</data-lsp>:  string  =  "blue";switch (<data-lsp lsp="const color: string">color</data-lsp>) {  case  "red":  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is red.");  break;  case  "blue":  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is blue.");  break;  default:  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is neither red nor blue.");}'Color is blue.'`
```

```
typescript`const  <data-lsp lsp="const color: string">color</data-lsp>:  string  =  "blue";switch (<data-lsp lsp="const color: string">color</data-lsp>) {  case  "red":  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is red.");  break;  case  "blue":  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is blue.");  break;  default:  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Color is neither red nor blue.");}'Color is blue.'`
```

### 型の絞り込み​

+   条件分岐を利用すると、その節内では型が自動的に絞り込まれる(制御フロー分析と型ガードによる型の絞り込み)。

```
typescript`let <data-lsp lsp="let value: string | number">value</data-lsp>:  string  |  number;// 50%の確率でstring 型またはnumber 型の値を代入する<data-lsp lsp="let value: string | number">value</data-lsp> =  <data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.random(): number">random</data-lsp>() <  0.5  ?  "Hello"  :  100;if (typeof <data-lsp lsp="let value: string | number">value</data-lsp> ===  "string") {  // この節ではvalueはstring 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let value: string">value</data-lsp>.<data-lsp lsp="(method) String.toUpperCase(): string">toUpperCase</data-lsp>());} else {  // この節ではvalueはnumber 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let value: number">value</data-lsp> *  3);}`
```

```
typescript`let <data-lsp lsp="let value: string | number">value</data-lsp>:  string  |  number;// 50%の確率でstring 型またはnumber 型の値を代入する<data-lsp lsp="let value: string | number">value</data-lsp> =  <data-lsp lsp="var Math: Math">Math</data-lsp>.<data-lsp lsp="(method) Math.random(): number">random</data-lsp>() <  0.5  ?  "Hello"  :  100;if (typeof <data-lsp lsp="let value: string | number">value</data-lsp> ===  "string") {  // この節ではvalueはstring 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let value: string">value</data-lsp>.<data-lsp lsp="(method) String.toUpperCase(): string">toUpperCase</data-lsp>());} else {  // この節ではvalueはnumber 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="let value: number">value</data-lsp> *  3);}`
```

## 関数​

+   TypeScriptではアロー関数や関数宣言に型注釈をつけることができる。

### アロー関数​

```
typescript`const  <data-lsp lsp="const greet: (name: string) => string">greet</data-lsp>  = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string  => {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}`;};<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const greet: (name: string) => string">greet</data-lsp>("John"));'Hello John'`
```

```
typescript`const <data-lsp lsp="const greet: (name: string) => string">greet</data-lsp> = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string  => {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}`;};<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const greet: (name: string) => string">greet</data-lsp>("John"));'Hello John'`
```

### 関数宣言​

```
typescript`function  <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}`;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name: string): string">greet</data-lsp>("John"));'Hello John'`
```

```
typescript`function <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string):  string {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}`;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name: string): string">greet</data-lsp>("John"));'Hello John'`
```

### 分割代入引数​

+   関数の引数に配列またはオブジェクトリテラルを展開することができる(分割代入引数)。

```
typescript`const  <data-lsp lsp="const printCoord: ({ x, y }: {
    x: number;
    y: number;
}) => void">printCoord</data-lsp>  = ({ <data-lsp lsp="(parameter) x: number">x</data-lsp>, <data-lsp lsp="(parameter) y: number">y</data-lsp> }: { <data-lsp lsp="(property) x: number">x</data-lsp>:  number; <data-lsp lsp="(property) y: number">y</data-lsp>:  number }) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Coordinate is (${<data-lsp lsp="(parameter) x: number">x</data-lsp>}, ${<data-lsp lsp="(parameter) y: number">y</data-lsp>})`);};<data-lsp lsp="const printCoord: ({ x, y }: {
    x: number;
    y: number;
}) => void">printCoord</data-lsp>({ <data-lsp lsp="(property) x: number">x</data-lsp>:  10, <data-lsp lsp="(property) y: number">y</data-lsp>:  20 });'Coordinate is (10, 20)'`
```

```
typescript`const <data-lsp lsp="const printCoord: ({ x, y }: {
    x: number;
    y: number;
}) => void">printCoord</data-lsp> = ({ <data-lsp lsp="(parameter) x: number">x</data-lsp>, <data-lsp lsp="(parameter) y: number">y</data-lsp> }: { <data-lsp lsp="(property) x: number">x</data-lsp>:  number; <data-lsp lsp="(property) y: number">y</data-lsp>:  number }) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`Coordinate is (${<data-lsp lsp="(parameter) x: number">x</data-lsp>}, ${<data-lsp lsp="(parameter) y: number">y</data-lsp>})`);};<data-lsp lsp="const printCoord: ({ x, y }: {
    x: number;
    y: number;
}) => void">printCoord</data-lsp>({ <data-lsp lsp="(property) x: number">x</data-lsp>:  10, <data-lsp lsp="(property) y: number">y</data-lsp>:  20 });'Coordinate is (10, 20)'`
```

### 型ガード関数​

+   特定の型であることを判定する関数(型ガード関数)を利用することで、型が絞り込まれる。

```
typescript`function  <data-lsp lsp="function isString(value: any): value is string">isString</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>:  any): <data-lsp lsp="(parameter) value: any">value</data-lsp> is  string {  return  typeof <data-lsp lsp="(parameter) value: any">value</data-lsp> ===  "string";}function  <data-lsp lsp="function printLength(value: any): void">printLength</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>:  any) {  if (<data-lsp lsp="function isString(value: any): value is string">isString</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>)) {  // この節ではvalueはstring 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) value: string">value</data-lsp>.<data-lsp lsp="(property) String.length: number">length</data-lsp>); }}<data-lsp lsp="function printLength(value: any): void">printLength</data-lsp>("hello");5`
```

```
typescript`function <data-lsp lsp="function isString(value: any): value is string">isString</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>:  any): <data-lsp lsp="(parameter) value: any">value</data-lsp> is  string {  return  typeof <data-lsp lsp="(parameter) value: any">value</data-lsp> ===  "string";}function <data-lsp lsp="function printLength(value: any): void">printLength</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>:  any) {  if (<data-lsp lsp="function isString(value: any): value is string">isString</data-lsp>(<data-lsp lsp="(parameter) value: any">value</data-lsp>)) {  // この節ではvalueはstring 型として扱われる  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) value: string">value</data-lsp>.<data-lsp lsp="(property) String.length: number">length</data-lsp>); }}<data-lsp lsp="function printLength(value: any): void">printLength</data-lsp>("hello");5`
```

### オプション引数​

+   関数の引数には`?`をつけることで任意とすることができる(オプション引数)。

```
typescript`function  <data-lsp lsp="function greet(name?: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>?:  string) {  if (<data-lsp lsp="(parameter) name: string | undefined">name</data-lsp> ===  <data-lsp lsp="var undefined">undefined</data-lsp>) {  return  "Hello!"; } else {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`; }}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>("John"));'Hello John!'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>());'Hello!'`
```

```
typescript`function <data-lsp lsp="function greet(name?: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>?:  string) {  if (<data-lsp lsp="(parameter) name: string | undefined">name</data-lsp> ===  <data-lsp lsp="var undefined">undefined</data-lsp>) {  return  "Hello!"; } else {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`; }}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>("John"));'Hello John!'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>());'Hello!'`
```

### デフォルト引数​

+   関数の引数には`=`を使ってデフォルトの値を設定することができる(デフォルト引数)。

```
typescript`function  <data-lsp lsp="function greet(name?: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string  =  "Mystery") {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>("John"));'Hello John!'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>());'Hello Mystery!'`
```

```
typescript`function <data-lsp lsp="function greet(name?: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string  =  "Mystery") {  return  `Hello ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>("John"));'Hello John!'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function greet(name?: string): string">greet</data-lsp>());'Hello Mystery!'`
```

### 残余引数​

+   `...`を使って残余引数(任意の数の引数)を設定することができる。

```
typescript`function  <data-lsp lsp="function sum(...numbers: number[]): number">sum</data-lsp>(...<data-lsp lsp="(parameter) numbers: number[]">numbers</data-lsp>:  number[]) {  return  <data-lsp lsp="(parameter) numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.reduce(callbackfn: (previousValue: number, currentValue: number, currentIndex: number, array: number[]) => number, initialValue: number): number (+2 overloads)">reduce</data-lsp>((<data-lsp lsp="(parameter) total: number">total</data-lsp>, <data-lsp lsp="(parameter) num: number">num</data-lsp>) => <data-lsp lsp="(parameter) total: number">total</data-lsp> + <data-lsp lsp="(parameter) num: number">num</data-lsp>,  0);}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function sum(...numbers: number[]): number">sum</data-lsp>(1,  2,  3,  4,  5));15`
```

```
typescript`function <data-lsp lsp="function sum(...numbers: number[]): number">sum</data-lsp>(...<data-lsp lsp="(parameter) numbers: number[]">numbers</data-lsp>:  number[]) {  return  <data-lsp lsp="(parameter) numbers: number[]">numbers</data-lsp>.<data-lsp lsp="(method) Array<number>.reduce(callbackfn: (previousValue: number, currentValue: number, currentIndex: number, array: number[]) => number, initialValue: number): number (+2 overloads)">reduce</data-lsp>((<data-lsp lsp="(parameter) total: number">total</data-lsp>, <data-lsp lsp="(parameter) num: number">num</data-lsp>) => <data-lsp lsp="(parameter) total: number">total</data-lsp> + <data-lsp lsp="(parameter) num: number">num</data-lsp>,  0);}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function sum(...numbers: number[]): number">sum</data-lsp>(1,  2,  3,  4,  5));15`
```

## クラス​

### クラス構文​

+   JavaScriptのクラス構文はそのまま利用できる。

+   フィールド宣言に型注釈をつけることができる。

```
typescript`class  <data-lsp lsp="class Person">Person</data-lsp> { <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string; <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; }  <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new  <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>();'My name is John and I am 20 years old.'`
```

```
typescript`class <data-lsp lsp="class Person">Person</data-lsp> { <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string; <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; } <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>();'My name is John and I am 20 years old.'`
```

### アクセス修飾子​

+   `public`(デフォルト)、`protected`、`private`の3つのアクセス修飾子が利用できる。

```
typescript`class  <data-lsp lsp="class Person">Person</data-lsp> {  public <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string;  private <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; }  <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new  <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(property) Person.name: string">name</data-lsp>); // 'John'が出力される<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: Person">john</data-lsp>.<data-err><data-lsp lsp="(property) Person.age: number">age</data-lsp></data-err>); // エラー（privateなのでアクセスできない）Property 'age' is private and only accessible within class 'Person'.2341Property 'age' is private and only accessible within class 'Person'.`
```

```
typescript`class <data-lsp lsp="class Person">Person</data-lsp> {  public <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string;  private <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; } <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(property) Person.name: string">name</data-lsp>); // 'John'が出力される<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const john: Person">john</data-lsp>.<data-err><data-lsp lsp="(property) Person.age: number">age</data-lsp></data-err>); // エラー（privateなのでアクセスできない）Property 'age' is private and only accessible within class 'Person'.2341Property 'age' is private and only accessible within class 'Person'.`
```

### クラスのreadonly 修飾子​

+   `readonly`修飾子をつけたプロパティは、読み取り専用となる。

+   `readonly`修饰符可以与访问修饰符结合使用。

```
typescript`class  <data-lsp lsp="class Person">Person</data-lsp> {  readonly <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string;  private  readonly <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; }  <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new  <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-err><data-lsp lsp="(property) Person.name: any">name</data-lsp></data-err> =  "Tom"; // エラー（readonlyのため変更不可）Cannot assign to 'name' because it is a read-only property.2540Cannot assign to 'name' because it is a read-only property.`
```

```
typescript`class <data-lsp lsp="class Person">Person</data-lsp> {  readonly <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string;  private  readonly <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string, <data-lsp lsp="(parameter) age: number">age</data-lsp>:  number) {  this.<data-lsp lsp="(property) Person.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>;  this.<data-lsp lsp="(property) Person.age: number">age</data-lsp> = <data-lsp lsp="(parameter) age: number">age</data-lsp>; } <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-err><data-lsp lsp="(property) Person.name: any">name</data-lsp></data-err> =  "Tom"; // エラー（readonlyのため変更不可）Cannot assign to 'name' because it is a read-only property.2540Cannot assign to 'name' because it is a read-only property.`
```

### 构造函数简写​

+   TypeScript 允许在构造函数参数上使用访问修饰符，从而自动定义该字段(constructor shorthand)。

+   这样可以简化代码。

```
typescript`class  <data-lsp lsp="class Person">Person</data-lsp> {  constructor(public <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string,  private <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number) {}  <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new  <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>();'My name is John and I am 20 years old.'`
```

```
typescript`class <data-lsp lsp="class Person">Person</data-lsp> {  constructor(public <data-lsp lsp="(property) Person.name: string">name</data-lsp>:  string,  private <data-lsp lsp="(property) Person.age: number">age</data-lsp>:  number) {} <data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`My name is ${this.<data-lsp lsp="(property) Person.name: string">name</data-lsp>} and I am ${this.<data-lsp lsp="(property) Person.age: number">age</data-lsp>} years old.`); }}const  <data-lsp lsp="const john: Person">john</data-lsp>  =  new <data-lsp lsp="constructor Person(name: string, age: number): Person">Person</data-lsp>("John",  20);<data-lsp lsp="const john: Person">john</data-lsp>.<data-lsp lsp="(method) Person.introduce(): void">introduce</data-lsp>();'My name is John and I am 20 years old.'`
```

### 字段的初始化器​

+   可以在字段声明时直接设置初始值(字段的初始化子)。

```
typescript`class  <data-lsp lsp="class Counter">Counter</data-lsp> { <data-lsp lsp="(property) Counter.count: number">count</data-lsp> =  0; // 初期値を0に設定  //    ^^^初期化子  <data-lsp lsp="(method) Counter.increment(): void">increment</data-lsp>():  void {  this.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>++; }}const  <data-lsp lsp="const counter: Counter">counter</data-lsp>  =  new  <data-lsp lsp="constructor Counter(): Counter">Counter</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>);0<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(method) Counter.increment(): void">increment</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>);1`
```

```
typescript`class <data-lsp lsp="class Counter">Counter</data-lsp> { <data-lsp lsp="(property) Counter.count: number">count</data-lsp> =  0; // 初期値を0に設定  //    ^^^初期化子 <data-lsp lsp="(method) Counter.increment(): void">increment</data-lsp>():  void {  this.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>++; }}const  <data-lsp lsp="const counter: Counter">counter</data-lsp>  =  new <data-lsp lsp="constructor Counter(): Counter">Counter</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>);0<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(method) Counter.increment(): void">increment</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const counter: Counter">counter</data-lsp>.<data-lsp lsp="(property) Counter.count: number">count</data-lsp>);1`
```

### 静态字段和静态方法​

+   使用`static`关键字，可以定义与类本身相关联的字段和方法，而不是实例(静态字段、静态方法)。

```
typescript`class  <data-lsp lsp="class MyClass">MyClass</data-lsp> {  static <data-lsp lsp="(property) MyClass.x: number">x</data-lsp> =  0;  static  <data-lsp lsp="(method) MyClass.printX(): void">printX</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="class MyClass">MyClass</data-lsp>.<data-lsp lsp="(property) MyClass.x: number">x</data-lsp>); }}<data-lsp lsp="class MyClass">MyClass</data-lsp>.<data-lsp lsp="(method) MyClass.printX(): void">printX</data-lsp>();0`
```

```
typescript`class <data-lsp lsp="class MyClass">MyClass</data-lsp> {  static <data-lsp lsp="(property) MyClass.x: number">x</data-lsp> =  0;  static <data-lsp lsp="(method) MyClass.printX(): void">printX</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="class MyClass">MyClass</data-lsp>.<data-lsp lsp="(property) MyClass.x: number">x</data-lsp>); }}<data-lsp lsp="class MyClass">MyClass</data-lsp>.<data-lsp lsp="(method) MyClass.printX(): void">printX</data-lsp>();0`
```

### this 类型​

+   通过在方法内返回`this`，可以实现方法链，将方法调用串联起来(方法链)。

```
typescript`class  <data-lsp lsp="class MyClass">MyClass</data-lsp> { <data-lsp lsp="(property) MyClass.value: number">value</data-lsp> =  1;  <data-lsp lsp="(method) MyClass.increment(): this">increment</data-lsp>():  this {  this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp>++;  return  this; }  <data-lsp lsp="(method) MyClass.add(v: number): this">add</data-lsp>(<data-lsp lsp="(parameter) v: number">v</data-lsp>:  number):  this {  this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp> += <data-lsp lsp="(parameter) v: number">v</data-lsp>;  return  this; }  <data-lsp lsp="(method) MyClass.print(): this">print</data-lsp>():  this {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp>);  return  this; }}new  <data-lsp lsp="constructor MyClass(): MyClass">MyClass</data-lsp>().<data-lsp lsp="(method) MyClass.increment(): this">increment</data-lsp>().<data-lsp lsp="(method) MyClass.add(v: number): this">add</data-lsp>(3).<data-lsp lsp="(method) MyClass.print(): this">print</data-lsp>();5`
```

```
typescript`class <data-lsp lsp="class MyClass">MyClass</data-lsp> { <data-lsp lsp="(property) MyClass.value: number">value</data-lsp> =  1; <data-lsp lsp="(method) MyClass.increment(): this">increment</data-lsp>():  this {  this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp>++;  return  this; } <data-lsp lsp="(method) MyClass.add(v: number): this">add</data-lsp>(<data-lsp lsp="(parameter) v: number">v</data-lsp>:  number):  this {  this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp> += <data-lsp lsp="(parameter) v: number">v</data-lsp>;  return  this; } <data-lsp lsp="(method) MyClass.print(): this">print</data-lsp>():  this {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(this.<data-lsp lsp="(property) MyClass.value: number">value</data-lsp>);  return  this; }}new <data-lsp lsp="constructor MyClass(): MyClass">MyClass</data-lsp>().<data-lsp lsp="(method) MyClass.increment(): this">increment</data-lsp>().<data-lsp lsp="(method) MyClass.add(v: number): this">add</data-lsp>(3).<data-lsp lsp="(method) MyClass.print(): this">print</data-lsp>();5`
```

### 类的继承​

+   使用`extends`关键字，可以进行类的继承。

+   超类的属性和方法的值可以从子类中访问。

```
typescript`class  <data-lsp lsp="class Animal">Animal</data-lsp> { <data-lsp lsp="(property) Animal.name: string">name</data-lsp>:  string;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  this.<data-lsp lsp="(property) Animal.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>; }  <data-lsp lsp="(method) Animal.greet(): string">greet</data-lsp>():  string {  return  `Hello, my name is ${this.<data-lsp lsp="(property) Animal.name: string">name</data-lsp>}`; }}class  <data-lsp lsp="class Dog">Dog</data-lsp>  extends  <data-lsp lsp="class Animal">Animal</data-lsp> {  <data-lsp lsp="(method) Dog.bark(): string">bark</data-lsp>():  string {  return  "Woof!"; }}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new  <data-lsp lsp="constructor Dog(name: string): Dog">Dog</data-lsp>("Max");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Animal.greet(): string">greet</data-lsp>());'Hello, my name is Max'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Dog.bark(): string">bark</data-lsp>());'Woof!'`
```

```
typescript`class <data-lsp lsp="class Animal">Animal</data-lsp> { <data-lsp lsp="(property) Animal.name: string">name</data-lsp>:  string;  constructor(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  this.<data-lsp lsp="(property) Animal.name: string">name</data-lsp> = <data-lsp lsp="(parameter) name: string">name</data-lsp>; } <data-lsp lsp="(method) Animal.greet(): string">greet</data-lsp>():  string {  return  `Hello, my name is ${this.<data-lsp lsp="(property) Animal.name: string">name</data-lsp>}`; }}class <data-lsp lsp="class Dog">Dog</data-lsp> extends <data-lsp lsp="class Animal">Animal</data-lsp> { <data-lsp lsp="(method) Dog.bark(): string">bark</data-lsp>():  string {  return  "Woof!"; }}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new <data-lsp lsp="constructor Dog(name: string): Dog">Dog</data-lsp>("Max");<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Animal.greet(): string">greet</data-lsp>());'Hello, my name is Max'<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Dog.bark(): string">bark</data-lsp>());'Woof!'`
```

### `instanceof`运算符​

+   `instanceof`运算符用于判断对象是否为特定类的实例。

```
typescript`class  <data-lsp lsp="class Animal">Animal</data-lsp> {}class  <data-lsp lsp="class Dog">Dog</data-lsp>  extends  <data-lsp lsp="class Animal">Animal</data-lsp> {}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new  <data-lsp lsp="constructor Dog(): Dog">Dog</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp> instanceof  <data-lsp lsp="class Dog">Dog</data-lsp>);true<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp> instanceof  <data-lsp lsp="class Animal">Animal</data-lsp>);true`
```

```
typescript`class <data-lsp lsp="class Animal">Animal</data-lsp> {}class <data-lsp lsp="class Dog">Dog</data-lsp> extends <data-lsp lsp="class Animal">Animal</data-lsp> {}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new <data-lsp lsp="constructor Dog(): Dog">Dog</data-lsp>();<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp> instanceof <data-lsp lsp="class Dog">Dog</data-lsp>);true<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const dog: Dog">dog</data-lsp> instanceof <data-lsp lsp="class Animal">Animal</data-lsp>);true`
```

### 抽象类​

+   使用`abstract`关键字，可以定义抽象类。

+   抽象类不能实例化，而是用于其他类的基类继承。

```
typescript`abstract  class  <data-lsp lsp="class Animal">Animal</data-lsp> {  abstract  <data-lsp lsp="(method) Animal.makeSound(): void">makeSound</data-lsp>():  void;  <data-lsp lsp="(method) Animal.move(): void">move</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("roaming the earth..."); }}class  <data-lsp lsp="class Dog">Dog</data-lsp>  extends  <data-lsp lsp="class Animal">Animal</data-lsp> {  <data-lsp lsp="(method) Dog.makeSound(): void">makeSound</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Woof Woof"); }}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new  <data-lsp lsp="constructor Dog(): Dog">Dog</data-lsp>();<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Animal.move(): void">move</data-lsp>();'roaming the earth...'<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Dog.makeSound(): void">makeSound</data-lsp>();'Woof Woof'`
```

```
typescript`abstract  class <data-lsp lsp="class Animal">Animal</data-lsp> {  abstract <data-lsp lsp="(method) Animal.makeSound(): void">makeSound</data-lsp>():  void; <data-lsp lsp="(method) Animal.move(): void">move</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("roaming the earth..."); }}class <data-lsp lsp="class Dog">Dog</data-lsp> extends <data-lsp lsp="class Animal">Animal</data-lsp> { <data-lsp lsp="(method) Dog.makeSound(): void">makeSound</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Woof Woof"); }}const  <data-lsp lsp="const dog: Dog">dog</data-lsp>  =  new <data-lsp lsp="constructor Dog(): Dog">Dog</data-lsp>();<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Animal.move(): void">move</data-lsp>();'roaming the earth...'<data-lsp lsp="const dog: Dog">dog</data-lsp>.<data-lsp lsp="(method) Dog.makeSound(): void">makeSound</data-lsp>();'Woof Woof'`
```

### 获取器和设置器​

+   获取器和设置器是用于获取和设置对象属性的方法。

+   获取器使用`get`关键字，设置器使用`set`关键字定义。

```
typescript`class  <data-lsp lsp="class Circle">Circle</data-lsp> {  private <data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) radius: number">radius</data-lsp>:  number) {  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp> = <data-lsp lsp="(parameter) radius: number">radius</data-lsp>; }  // ゲッター  get  <data-lsp lsp="(getter) Circle.radius: number">radius</data-lsp>():  number {  return  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp>; }  // セッター  set  <data-lsp lsp="(setter) Circle.radius: number">radius</data-lsp>(<data-lsp lsp="(parameter) radius: number">radius</data-lsp>:  number) {  if (<data-lsp lsp="(parameter) radius: number">radius</data-lsp> <=  0) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("Invalid radius value"); }  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp> = <data-lsp lsp="(parameter) radius: number">radius</data-lsp>; }}const  <data-lsp lsp="const circle: Circle">circle</data-lsp>  =  new  <data-lsp lsp="constructor Circle(radius: number): Circle">Circle</data-lsp>(5);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp>);5<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp> =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp>);3<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp> =  -2;// 例外: 'Invalid radius value'`
```

```
typescript`class <data-lsp lsp="class Circle">Circle</data-lsp> {  private <data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp>:  number;  constructor(<data-lsp lsp="(parameter) radius: number">radius</data-lsp>:  number) {  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp> = <data-lsp lsp="(parameter) radius: number">radius</data-lsp>; }  // ゲッター  get <data-lsp lsp="(getter) Circle.radius: number">radius</data-lsp>():  number {  return  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp>; }  // セッター  set <data-lsp lsp="(setter) Circle.radius: number">radius</data-lsp>(<data-lsp lsp="(parameter) radius: number">radius</data-lsp>:  number) {  if (<data-lsp lsp="(parameter) radius: number">radius</data-lsp> <=  0) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("Invalid radius value"); }  this.<data-lsp lsp="(property) Circle._radius: number">_radius</data-lsp> = <data-lsp lsp="(parameter) radius: number">radius</data-lsp>; }}const  <data-lsp lsp="const circle: Circle">circle</data-lsp>  =  new <data-lsp lsp="constructor Circle(radius: number): Circle">Circle</data-lsp>(5);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp>);5<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp> =  3;<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp>);3<data-lsp lsp="const circle: Circle">circle</data-lsp>.<data-lsp lsp="(property) Circle.radius: number">radius</data-lsp> =  -2;// 例外: 'Invalid radius value'`
```

### 接口​

+   TypeScript 的接口具有定义属性、方法、类等形状的能力。

+   接口的主要目的是强制特定类或对象具有特定属性或方法。

```
typescript`interface  <data-lsp lsp="interface Printable">Printable</data-lsp> {  <data-lsp lsp="(method) Printable.print(): void">print</data-lsp>():  void;}class  <data-lsp lsp="class MyClass">MyClass</data-lsp>  implements  <data-lsp lsp="interface Printable">Printable</data-lsp> {  <data-lsp lsp="(method) MyClass.print(): void">print</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello, world!"); }}`
```

```
typescript`interface <data-lsp lsp="interface Printable">Printable</data-lsp> { <data-lsp lsp="(method) Printable.print(): void">print</data-lsp>():  void;}class <data-lsp lsp="class MyClass">MyClass</data-lsp> implements <data-lsp lsp="interface Printable">Printable</data-lsp> { <data-lsp lsp="(method) MyClass.print(): void">print</data-lsp>():  void {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello, world!"); }}`
```

### 接口语法​

+   TypeScript 的接口可以定义对象的形状。

+   接口可以描述属性和方法的签名。

```
typescript`interface  <data-lsp lsp="interface Point">Point</data-lsp> {  readonly <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  number;  readonly <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  number;  <data-lsp lsp="(method) Point.sum(): number">sum</data-lsp>():  number;}const  <data-lsp lsp="const point: Point">point</data-lsp>:  <data-lsp lsp="interface Point">Point</data-lsp>  = { <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  10, <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  20,  <data-lsp lsp="(method) Point.sum(): number">sum</data-lsp>:  function () {  return  this.<data-lsp lsp="(property) Point.x: number">x</data-lsp> +  this.<data-lsp lsp="(property) Point.y: number">y</data-lsp>; },};`
```

```
typescript`interface <data-lsp lsp="interface Point">Point</data-lsp> {  readonly <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  number;  readonly <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  number; <data-lsp lsp="(method) Point.sum(): number">sum</data-lsp>():  number;}const  <data-lsp lsp="const point: Point">point</data-lsp>: <data-lsp lsp="interface Point">Point</data-lsp> = { <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  10, <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  20, <data-lsp lsp="(method) Point.sum(): number">sum</data-lsp>:  function () {  return  this.<data-lsp lsp="(property) Point.x: number">x</data-lsp> +  this.<data-lsp lsp="(property) Point.y: number">y</data-lsp>; },};`
```

### 接口的 readonly 修饰符​

+   使用接口内的 readonly 修饰符，可以将属性设置为只读。

+   这样一来，一旦设置了属性的值，就无法再次更改。

```
typescript`interface  <data-lsp lsp="interface Point">Point</data-lsp> {  readonly <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  number;  readonly <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  number;}const  <data-lsp lsp="const p1: Point">p1</data-lsp>:  <data-lsp lsp="interface Point">Point</data-lsp>  = { <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  10, <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  20 };<data-lsp lsp="const p1: Point">p1</data-lsp>.<data-err><data-lsp lsp="(property) Point.x: any">x</data-lsp></data-err> =  5;Cannot assign to 'x' because it is a read-only property.2540Cannot assign to 'x' because it is a read-only property.`
```

```
typescript`interface <data-lsp lsp="interface Point">Point</data-lsp> {  readonly <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  number;  readonly <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  number;}const  <data-lsp lsp="const p1: Point">p1</data-lsp>: <data-lsp lsp="interface Point">Point</data-lsp> = { <data-lsp lsp="(property) Point.x: number">x</data-lsp>:  10, <data-lsp lsp="(property) Point.y: number">y</data-lsp>:  20 };<data-lsp lsp="const p1: Point">p1</data-lsp>.<data-err><data-lsp lsp="(property) Point.x: any">x</data-lsp></data-err> =  5;Cannot assign to 'x' because it is a read-only property.2540Cannot assign to 'x' because it is a read-only property.`
```

## 异常处理​

+   TypeScript 支持使用 try / catch / finally 块进行异常处理。

+   如果发生异常（即抛出错误对象），则执行 catch 块。

```
typescript`try {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("An error occurred!");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var error: unknown">error</data-lsp>);}`
```

```
typescript`try {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("An error occurred!");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var error: unknown">error</data-lsp>);}`
```

### try-catch-finally 语法​

+   try 块内的代码用于检测错误，catch 块用于处理错误。

+   finally 块会在无论有无错误都执行。

```
typescript`try {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("Oops, something went wrong.");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var error: unknown">error</data-lsp>);} finally {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("This is the finally block. It always gets executed.");}`
```

```
typescript`try {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("Oops, something went wrong.");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="var error: unknown">error</data-lsp>);} finally {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("This is the finally block. It always gets executed.");}`
```

### 异常类​

+   TypeScript 还允许创建自定义错误类。

+   可以创建继承自 Error 类的自定义类，以创建特定的错误类型。

```
typescript`class  <data-lsp lsp="class CustomError">CustomError</data-lsp>  extends  <data-lsp lsp="var Error: ErrorConstructor">Error</data-lsp> { <data-lsp lsp="(property) CustomError.code: string">code</data-lsp> =  "CustomError";  constructor(<data-lsp lsp="(parameter) message: string | undefined">message</data-lsp>?:  string) {  super(<data-lsp lsp="(parameter) message: string | undefined">message</data-lsp>); }}try {  throw  new  <data-lsp lsp="constructor CustomError(message?: string): CustomError">CustomError</data-lsp>("This is a custom error");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  if (<data-lsp lsp="var error: unknown">error</data-lsp> instanceof  <data-lsp lsp="class CustomError">CustomError</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`${<data-lsp lsp="var error: CustomError">error</data-lsp>.<data-lsp lsp="(property) CustomError.code: string">code</data-lsp>}: ${<data-lsp lsp="var error: CustomError">error</data-lsp>.<data-lsp lsp="(property) Error.message: string">message</data-lsp>}`); }}`
```

```
typescript`class <data-lsp lsp="class CustomError">CustomError</data-lsp> extends  <data-lsp lsp="var Error: ErrorConstructor">Error</data-lsp> { <data-lsp lsp="(property) CustomError.code: string">code</data-lsp> =  "CustomError";  constructor(<data-lsp lsp="(parameter) message: string | undefined">message</data-lsp>?:  string) { super(<data-lsp lsp="(parameter) message: string | undefined">message</data-lsp>); }}try {  throw  new <data-lsp lsp="constructor CustomError(message?: string): CustomError">CustomError</data-lsp>("This is a custom error");} catch (<data-lsp lsp="var error: unknown">error</data-lsp>) {  if (<data-lsp lsp="var error: unknown">error</data-lsp> instanceof <data-lsp lsp="class CustomError">CustomError</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(`${<data-lsp lsp="var error: CustomError">error</data-lsp>.<data-lsp lsp="(property) CustomError.code: string">code</data-lsp>}: ${<data-lsp lsp="var error: CustomError">error</data-lsp>.<data-lsp lsp="(property) Error.message: string">message</data-lsp>}`); }}`
```

## 异步处理​

+   TypeScript 支持异步编程，可以有效处理代码中的耗时操作。

### Promise​

+   Promise 表示异步操作的最终完成（或失败）以及其结果值。

```
typescript`const  <data-lsp lsp="const promise: Promise<unknown>">promise</data-lsp>  =  new  <data-lsp lsp="var Promise: PromiseConstructor
new <unknown>(executor: (resolve: (value: unknown) => void, reject: (reason?: any) => void) => void) => Promise<unknown>">Promise</data-lsp>((<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>, <data-lsp lsp="(parameter) reject: (reason?: any) => void">reject</data-lsp>) => {  <data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => {  <data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>("Promise resolved"); },  2000);});<data-lsp lsp="const promise: Promise<unknown>">promise</data-lsp>.<data-lsp lsp="(method) Promise<unknown>.then<void, never>(onfulfilled?: ((value: unknown) => void | PromiseLike<void>) | null | undefined, onrejected?: ((reason: any) => PromiseLike<never>) | null | undefined): Promise<...>">then</data-lsp>((<data-lsp lsp="(parameter) data: unknown">data</data-lsp>) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) data: unknown">data</data-lsp>);});'Promise resolved'`
```

```
typescript`const  <data-lsp lsp="const promise: Promise<unknown>">promise</data-lsp>  =  new  <data-lsp lsp="var Promise: PromiseConstructor
new <unknown>(executor: (resolve: (value: unknown) => void, reject: (reason?: any) => void) => void) => Promise<unknown>">Promise</data-lsp>((<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>, <data-lsp lsp="(parameter) reject: (reason?: any) => void">reject</data-lsp>) => { <data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => { <data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>("Promise resolved"); },  2000);});<data-lsp lsp="const promise: Promise<unknown>">promise</data-lsp>.<data-lsp lsp="(method) Promise<unknown>.then<void, never>(onfulfilled?: ((value: unknown) => void | PromiseLike<void>) | null | undefined, onrejected?: ((reason: any) => PromiseLike<never>) | null | undefined): Promise<...>">then</data-lsp>((<data-lsp lsp="(parameter) data: unknown">data</data-lsp>) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(parameter) data: unknown">data</data-lsp>);});'Promise resolved'`
```

### async/await 语法​

+   引入了 async 语法和 await 语法，以更直观地编写异步代码。

+   使用 async/await 语法，可以将异步代码编写得就像同步代码一样。

```
typescript`function  <data-lsp lsp="function delay(ms: number): Promise<unknown>">delay</data-lsp>(<data-lsp lsp="(parameter) ms: number">ms</data-lsp>:  number) {  return  new  <data-lsp lsp="var Promise: PromiseConstructor
new <unknown>(executor: (resolve: (value: unknown) => void, reject: (reason?: any) => void) => void) => Promise<unknown>">Promise</data-lsp>((<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>) =>  <data-lsp lsp="function setTimeout(callback: (args: void) => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>, <data-lsp lsp="(parameter) ms: number">ms</data-lsp>));}async  function  <data-lsp lsp="function asyncFunction(): Promise<void>">asyncFunction</data-lsp>() {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Start");  await  <data-lsp lsp="function delay(ms: number): Promise<unknown>">delay</data-lsp>(2000);  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("End");}<data-lsp lsp="function asyncFunction(): Promise<void>">asyncFunction</data-lsp>();'Start'// 2 秒後'End'`
```

```
typescript`function <data-lsp lsp="function delay(ms: number): Promise<unknown>">delay</data-lsp>(<data-lsp lsp="(parameter) ms: number">ms</data-lsp>:  number) {  return  new  <data-lsp lsp="var Promise: PromiseConstructor
new <unknown>(executor: (resolve: (value: unknown) => void, reject: (reason?: any) => void) => void) => Promise<unknown>">Promise</data-lsp>((<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>) => <data-lsp lsp="function setTimeout(callback: (args: void) => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(<data-lsp lsp="(parameter) resolve: (value: unknown) => void">resolve</data-lsp>, <data-lsp lsp="(parameter) ms: number">ms</data-lsp>));}async  function <data-lsp lsp="function asyncFunction(): Promise<void>">asyncFunction</data-lsp>() {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Start");  await <data-lsp lsp="function delay(ms: number): Promise<unknown>">delay</data-lsp>(2000);  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("End");}<data-lsp lsp="function asyncFunction(): Promise<void>">asyncFunction</data-lsp>();'Start'// 2 秒後'End'`
```

## 泛型​

+   使用 TypeScript 的泛型，可以提高类型的可重用性和一致性。

+   使用泛型，可以引入类型变量，从而泛化部分功能。

```
typescript`// Tが型変数 function  <data-lsp lsp="function identity<T>(arg: T): T">identity</data-lsp><<data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>>(<data-lsp lsp="(parameter) arg: T">arg</data-lsp>:  <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>):  <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp> {  return <data-lsp lsp="(parameter) arg: T">arg</data-lsp>;}// 型変数 Tにstringを割り当てるconst  <data-lsp lsp="const output1: string" style="border-bottom:solid 2px lightgrey">output1</data-lsp>  =  <data-lsp lsp="function identity<string>(arg: string): string">identity</data-lsp><string>("myString");` `const output1: string// 型変数 Tにnumberを割り当てるconst  <data-lsp lsp="const output2: number" style="border-bottom:solid 2px lightgrey">output2</data-lsp>  =  <data-lsp lsp="function identity<number>(arg: number): number">identity</data-lsp><number>(100);` `const output2: number`

```

typescript`// Tが型変数 function <data-lsp lsp="function identity<T>(arg: T): T">identity</data-lsp><<data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>>(<data-lsp lsp="(parameter) arg: T">arg</data-lsp>: <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>): <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp> {  return <data-lsp lsp="(parameter) arg: T">arg</data-lsp>;}// 型変数 Tにstringを割り当てるconst  <data-lsp lsp="const output1: string" style="border-bottom:solid 2px lightgrey">output1</data-lsp>  = <data-lsp lsp="function identity<string>(arg: string): string">identity</data-lsp><string>("myString");` `const output1: string// 型変数 Tにnumberを割り当てるconst  <data-lsp lsp="const output2: number" style="border-bottom:solid 2px lightgrey">output2</data-lsp>  = <data-lsp lsp="function identity<number>(arg: number): number">identity</data-lsp><number>(100);` `const output2: number`

## モジュール​

+   TypeScriptのモジュールシステムは、他のモジュールと共有するコードと、モジュール内部限定のコードとを分けることを可能にする(モジュール)。

```
greeter.tstypescript`export  function  <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  return  `Hello, ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}`
```

```
greeter.tstypescript`export  function <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  return  `Hello, ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function greet(name: string): string
import greet">greet</data-lsp> } from  "./greeter";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) greet(name: string): string
import greet">greet</data-lsp>("TypeScript"));'Hello, TypeScript!'`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function greet(name: string): string
import greet">greet</data-lsp> } from  "./greeter";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) greet(name: string): string
import greet">greet</data-lsp>("TypeScript"));'Hello, TypeScript!'`
```

### importとexport​

+   モジュール内で定義した関数や変数を外部に公開するには、exportを使用する。

+   モジュールが公開した関数や変数を利用するには、importを使用する。

```
math.tstypescript`export  function  <data-lsp lsp="function square(x: number): number">square</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp>;}export  function  <data-lsp lsp="function cube(x: number): number">cube</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp>;}`
```

```
math.tstypescript`export  function <data-lsp lsp="function square(x: number): number">square</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp>;}export  function <data-lsp lsp="function cube(x: number): number">cube</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp> * <data-lsp lsp="(parameter) x: number">x</data-lsp>;}`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function square(x: number): number
import square">square</data-lsp>, <data-lsp lsp="(alias) function cube(x: number): number
import cube">cube</data-lsp> } from  "./math";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) square(x: number): number
import square">square</data-lsp>(2));4<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) cube(x: number): number
import cube">cube</data-lsp>(2));8`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function square(x: number): number
import square">square</data-lsp>, <data-lsp lsp="(alias) function cube(x: number): number
import cube">cube</data-lsp> } from  "./math";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) square(x: number): number
import square">square</data-lsp>(2));4<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) cube(x: number): number
import cube">cube</data-lsp>(2));8`
```

### default export​

+   defaultキーワードを使用すると、モジュールがデフォルトで1つの値のみをエクスポートすることを意味する。

+   default exportは、importする際に別名を指定することが可能である。

```
greeter.tstypescript`export  default  function  <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  return  `Hello, ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}`
```

```
greeter.tstypescript`export  default  function <data-lsp lsp="function greet(name: string): string">greet</data-lsp>(<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) {  return  `Hello, ${<data-lsp lsp="(parameter) name: string">name</data-lsp>}!`;}`
```

```
main.tstypescript`import <data-lsp lsp="(alias) function greetFunction(name: string): string
import greetFunction">greetFunction</data-lsp> from  "./greeter";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) greetFunction(name: string): string
import greetFunction">greetFunction</data-lsp>("TypeScript"));'Hello, TypeScript!'`
```

```
main.tstypescript`import <data-lsp lsp="(alias) function greetFunction(name: string): string
import greetFunction">greetFunction</data-lsp> from  "./greeter";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) greetFunction(name: string): string
import greetFunction">greetFunction</data-lsp>("TypeScript"));'Hello, TypeScript!'`
```

### 再 export​

+   モジュールは、別のモジュールからエクスポートされたものを再エクスポートすることができる。

```
math.tstypescript`export  function  <data-lsp lsp="function add(x: number, y: number): number">add</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number, <data-lsp lsp="(parameter) y: number">y</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> + <data-lsp lsp="(parameter) y: number">y</data-lsp>;}`
```

```
math.tstypescript`export  function <data-lsp lsp="function add(x: number, y: number): number">add</data-lsp>(<data-lsp lsp="(parameter) x: number">x</data-lsp>:  number, <data-lsp lsp="(parameter) y: number">y</data-lsp>:  number) {  return <data-lsp lsp="(parameter) x: number">x</data-lsp> + <data-lsp lsp="(parameter) y: number">y</data-lsp>;}`
```

```
index.tstypescript`// 再エクスポートexport { <data-lsp lsp="(alias) function add(x: number, y: number): number
export add">add</data-lsp> } from  "./math";`
```

```
index.tstypescript`// 再エクスポートexport { <data-lsp lsp="(alias) function add(x: number, y: number): number
export add">add</data-lsp> } from  "./math";`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function add(x: number, y: number): number
import add">add</data-lsp> } from  "./index";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) add(x: number, y: number): number
import add">add</data-lsp>(2,  3));5`
```

```
main.tstypescript`import { <data-lsp lsp="(alias) function add(x: number, y: number): number
import add">add</data-lsp> } from  "./index";<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="(alias) add(x: number, y: number): number
import add">add</data-lsp>(2,  3));5`
```

### type importとtype export​

+   型だけをエクスポート・インポートすることもできる。

```
types.tstypescript`export  type  <data-lsp lsp="type MyObject = {
    name: string;
    age: number;
}">MyObject</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};`
```

```
types.tstypescript`export  type <data-lsp lsp="type MyObject = {
    name: string;
    age: number;
}">MyObject</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};`
```

```
main.tstypescript`import  type { <data-lsp lsp="(alias) type MyObject = {
    name: string;
    age: number;
}
import MyObject">MyObject</data-lsp> } from  "./types";//     ^^^^型インポートconst  <data-lsp lsp="const obj: MyObject">obj</data-lsp>:  <data-lsp lsp="(alias) type MyObject = {
    name: string;
    age: number;
}
import MyObject">MyObject</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "TypeScript", <data-lsp lsp="(property) age: number">age</data-lsp>:  3,};`
```

```
main.tstypescript`import  type { <data-lsp lsp="(alias) type MyObject = {
    name: string;
    age: number;
}
import MyObject">MyObject</data-lsp> } from  "./types";//     ^^^^型インポートconst  <data-lsp lsp="const obj: MyObject">obj</data-lsp>: <data-lsp lsp="(alias) type MyObject = {
    name: string;
    age: number;
}
import MyObject">MyObject</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "TypeScript", <data-lsp lsp="(property) age: number">age</data-lsp>:  3,};`
```

## 型レベルプログラミング​

+   TypeScriptには、typeof 演算子やkeyof 演算子、ユーティリティータイプなど、型レベルでプログラミングをするためのさまざまな機能が搭載されている。

### typeof 型演算子​

+   typeof 演算子は、変数名から型を逆算できる。

```
typescript`const  <data-lsp lsp="const object: {
    name: string;
    version: number;
}">object</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "TypeScript", <data-lsp lsp="(property) version: number">version</data-lsp>:  3.9,};type  <data-lsp lsp="type ObjectType = {
    name: string;
    version: number;
}" style="border-bottom:solid 2px lightgrey">ObjectType</data-lsp>  =  typeof <data-lsp lsp="const object: {
    name: string;
    version: number;
}">object</data-lsp>;` `type ObjectType = {
    name: string;
    version: number;
}`

```

typescript`const  <data-lsp lsp="const object: {

    name: string;

    version: number;

}">object</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "TypeScript", <data-lsp lsp="(property) version: number">version</data-lsp>:  3.9,};type <data-lsp lsp="type ObjectType = {

    name: string;

    version: number;

}" style="border-bottom:solid 2px lightgrey">ObjectType</data-lsp> =  typeof <data-lsp lsp="const object: {

    name: string;

    version: number;

}">object</data-lsp>;` `type ObjectType = {

    name: string;

    version: number;

}`

### keyof 型演算子​

+   keyof 演算子を使うと、object 型のすべてのキーを文字列リテラルのユニオン型として取得できる。

```
typescript`type  <data-lsp lsp="type Point = {
    x: number;
    y: number;
}">Point</data-lsp>  = { <data-lsp lsp="(property) x: number">x</data-lsp>:  number; <data-lsp lsp="(property) y: number">y</data-lsp>:  number;};type  <data-lsp lsp="type Key = keyof Point" style="border-bottom:solid 2px lightgrey">Key</data-lsp>  =  keyof  <data-lsp lsp="type Point = {
    x: number;
    y: number;
}">Point</data-lsp>;` `type Key = keyof Pointconst  <data-lsp lsp="const key1: keyof Point">key1</data-lsp>:  <data-lsp lsp="type Key = keyof Point">Key</data-lsp>  =  "x"; // 代入 OKconst  <data-lsp lsp="const key2: keyof Point">key2</data-lsp>:  <data-lsp lsp="type Key = keyof Point">Key</data-lsp>  =  "y"; // 代入 OKconst  <data-err><data-lsp lsp="const key3: keyof Point">key3</data-lsp></data-err>:  <data-lsp lsp="type Key = keyof Point">Key</data-lsp>  =  "z"; // 代入不可 Type '"z"' is not assignable to type 'keyof Point'.2322Type '"z"' is not assignable to type 'keyof Point'.`

```

typescript`type <data-lsp lsp="type Point = {

    x: number;

    y: number;

}">Point</data-lsp> = { <data-lsp lsp="(property) x: number">x</data-lsp>:  number; <data-lsp lsp="(property) y: number">y</data-lsp>:  number;};type <data-lsp lsp="type Key = keyof Point" style="border-bottom:solid 2px lightgrey">Key</data-lsp> =  keyof <data-lsp lsp="type Point = {

    x: number;

    y: number;

}">Point</data-lsp>;` `type Key = keyof Pointconst  <data-lsp lsp="const key1: keyof Point">key1</data-lsp>: <data-lsp lsp="type Key = keyof Point">Key</data-lsp> =  "x"; // 代入 OKconst  <data-lsp lsp="const key2: keyof Point">key2</data-lsp>: <data-lsp lsp="type Key = keyof Point">Key</data-lsp> =  "y"; // 代入 OKconst  <data-lsp lsp="const key3: keyof Point">key3</data-lsp>: <data-lsp lsp="type Key = keyof Point">Key</data-lsp> =  "z"; // 代入不可 Type '"z"' is not assignable to type 'keyof Point'.2322Type '"z"' is not assignable to type 'keyof Point'.`

### ユーティリティ型​

+   TypeScriptは、既存の型から新しい型を作成するためのさまざまな一般的な型操作を提供している。

#### Required​

+   `Required`は、オプションプロパティーを必須プロパティーにするユーティリティ型。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age?: number | undefined;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number;};type  <data-lsp lsp="type RequiredPerson = {
    name: string;
    age: number;
}" style="border-bottom:solid 2px lightgrey">RequiredPerson</data-lsp>  =  <data-lsp lsp="type Required<T> = { [P in keyof T]-?: T[P]; }">Required</data-lsp><<data-lsp lsp="type Person = {
    name: string;
    age?: number | undefined;
}">Person</data-lsp>>;` `type RequiredPerson = {
    name: string;
    age: number;
}// ageがオプションでなくなっている点に注目`

```

typescript`type <data-lsp lsp="type Person = {

    name: string;

    age?: number | undefined;

}">Person</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number;};type <data-lsp lsp="type RequiredPerson = {

    name: string;

    age: number;

}" style="border-bottom:solid 2px lightgrey">RequiredPerson</data-lsp> = <data-lsp lsp="type Required<T> = { [P in keyof T]-?: T[P]; }">Required</data-lsp><<data-lsp lsp="type Person = {

    name: string;

    age?: number | undefined;

}">Person</data-lsp>>;` `type RequiredPerson = {

    name: string;

    age: number;

}// ageがオプションでなくなっている点に注目`

#### Partial​

+   `Partial`は、型のすべてのプロパティをオプションにするユーティリティ型。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type  <data-lsp lsp="type OptionalPerson = {
    name?: string | undefined;
    age?: number | undefined;
}" style="border-bottom:solid 2px lightgrey">OptionalPerson</data-lsp>  =  <data-lsp lsp="type Partial<T> = { [P in keyof T]?: T[P] | undefined; }">Partial</data-lsp><<data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>>;` `type OptionalPerson = {
    name?: string | undefined;
    age?: number | undefined;
}`

```

typescript`type <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type <data-lsp lsp="type OptionalPerson = {

    name?: string | undefined;

    age?: number | undefined;

}" style="border-bottom:solid 2px lightgrey">OptionalPerson</data-lsp> = <data-lsp lsp="type Partial<T> = { [P in keyof T]?: T[P] | undefined; }">Partial</data-lsp><<data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp>>;` `type OptionalPerson = {

    name?: string | undefined;

    age?: number | undefined;

}`

#### Readonly​

+   `Readonly`は、型のすべてのプロパティをreadonlyにするユーティリティ型。それらのプロパティは再代入できない。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type  <data-lsp lsp="type ReadonlyPerson = {
    readonly name: string;
    readonly age: number;
}" style="border-bottom:solid 2px lightgrey">ReadonlyPerson</data-lsp>  =  <data-lsp lsp="type Readonly<T> = { readonly [P in keyof T]: T[P]; }">Readonly</data-lsp><<data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>>;` `type ReadonlyPerson = {
    readonly name: string;
    readonly age: number;
}`

```

typescript`type <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type <data-lsp lsp="type ReadonlyPerson = {

    readonly name: string;

    readonly age: number;

}" style="border-bottom:solid 2px lightgrey">ReadonlyPerson</data-lsp> = <data-lsp lsp="type Readonly<T> = { readonly [P in keyof T]: T[P]; }">Readonly</data-lsp><<data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp>>;` `type ReadonlyPerson = {

    只读 名称: 字符串;

    只读 年龄: 数字;

}`

#### 记录​

+   `记录`是将对象的所有属性值设置为特定类型的实用程序类型。

```
typescript`type  <data-lsp lsp="type ThreeLetterRecord = {
    one: string;
    two: string;
    three: string;
}" style="border-bottom:solid 2px lightgrey">ThreeLetterRecord</data-lsp>  =  <data-lsp lsp="type Record<K extends string | number | symbol, T> = { [P in K]: T; }">Record</data-lsp><"one"  |  "two"  |  "three",  string>;` `type ThreeLetterRecord = {
    one: string;
    two: string;
    three: string;
}`

```

typescript`类型 <data-lsp lsp="type 三字母记录 = {

    一个: 字符串;

    二: 字符串;

    三: 字符串;

}" style="border-bottom:solid 2px lightgrey">三字母记录</data-lsp> = <data-lsp lsp="type 记录<K extends string | number | symbol, T> = { [P in K]: T; }">记录</data-lsp><"一个"  |  "二"  |  "三",  字符串>;` `类型 三字母记录 = {

    一个: 字符串;

    二: 字符串;

    三: 字符串;

}`

#### 挑选​

+   `挑选`是���对象中挑选特定属性的实用程序类型。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
    address: string;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number; <data-lsp lsp="(property) address: string">address</data-lsp>:  string;};type  <data-lsp lsp="type PersonNameAndAge = {
    name: string;
    age: number;
}" style="border-bottom:solid 2px lightgrey">PersonNameAndAge</data-lsp>  =  <data-lsp lsp="type Pick<T, K extends keyof T> = { [P in K]: T[P]; }">Pick</data-lsp><<data-lsp lsp="type Person = {
    name: string;
    age: number;
    address: string;
}">Person</data-lsp>,  "name"  |  "age">;` `type PersonNameAndAge = {
    name: string;
    age: number;
}`

```

typescript`类型 <data-lsp lsp="type 人员 = {

    名称: 字符串;

    年龄: 数字;

    地址: 字符串;

}">人员</data-lsp> = { <data-lsp lsp="(属性) 名称: 字符串">名称</data-lsp>:  字符串; <data-lsp lsp="(属性) 年龄: 数字">年龄</data-lsp>:  数字; <data-lsp lsp="(属性) 地址: 字符串">地址</data-lsp>:  字符串;};类型 <data-lsp lsp="type 人员名称和年龄 = {

    名称: 字符串;

    年龄: 数字;

}" style="border-bottom:solid 2px lightgrey">人员名称和年龄</data-lsp> = <data-lsp lsp="type 挑选<T, K extends keyof T> = { [P in K]: T[P]; }">挑选</data-lsp><<data-lsp lsp="type 人员 = {

    名称: 字符串;

    年龄: 数字;

    地址: 字符串;

}">人员</data-lsp>,  "名称"  |  "年龄">;` `类型 人员名称和年龄 = {

    名称: 字符串;

    年龄: 数字;

}`

#### 省略​

+   `省略`是创建省略对象特定属性的类型的实用程序类型。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
    address: string;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number; <data-lsp lsp="(property) address: string">address</data-lsp>:  string;};type  <data-lsp lsp="type PersonWithoutAddress = {
    name: string;
    age: number;
}" style="border-bottom:solid 2px lightgrey">PersonWithoutAddress</data-lsp>  =  <data-lsp lsp="type Omit<T, K extends string | number | symbol> = { [P in Exclude<keyof T, K>]: T[P]; }">Omit</data-lsp><<data-lsp lsp="type Person = {
    name: string;
    age: number;
    address: string;
}">Person</data-lsp>,  "address">;` `type PersonWithoutAddress = {
    name: string;
    age: number;
}`

```

typescript`类型 <data-lsp lsp="type 人员 = {

    名称: 字符串;

    年龄: 数字;

    地址: 字符串;

}">人员</data-lsp> = { <data-lsp lsp="(属性) 名称: 字符串">名称</data-lsp>:  字符串; <data-lsp lsp="(属性) 年龄: 数字">年龄</data-lsp>:  数字; <data-lsp lsp="(属性) 地址: 字符串">地址</data-lsp>:  字符串;};类型 <data-lsp lsp="type 无地址人员 = {

    名称: 字符串;

    年龄: 数字;

}" style="border-bottom:solid 2px lightgrey">无地址人员</data-lsp> = <data-lsp lsp="type Omit<T, K extends string | number | symbol> = { [P in Exclude<keyof T, K>]: T[P]; }">省略</data-lsp><<data-lsp lsp="type 人员 = {

    名称: 字符串;

    年龄: 数字;

    地址: 字符串;

}">人员</data-lsp>,  "地址">;` `类型 无地址人员 = {

    名称: 字符串;

    年龄: 数字;

}`

#### 排除​

+   `排除`是从联合类型中排除特定类型的实用程序类型。

```
typescript`type  <data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>  =  number  |  string  |  boolean;type  <data-lsp lsp="type T2 = string | number" style="border-bottom:solid 2px lightgrey">T2</data-lsp>  =  <data-lsp lsp="type Exclude<T, U> = T extends U ? never : T">Exclude</data-lsp><<data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>,  boolean>;` `type T2 = string | number`

```

typescript`类型 <data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp> =  数字  |  字符串  |  布尔;类型 <data-lsp lsp="type T2 = string | number" style="border-bottom:solid 2px lightgrey">T2</data-lsp> = <data-lsp lsp="type 排除<T, U> = T extends U ? never : T">排除</data-lsp><<data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>,  布尔>;` `类型 T2 = 字符串 | 数字`

#### 提取​

+   `提取`是提取两个联合类型的共同部分的实用程序类型。

```
typescript`type  <data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>  =  number  |  string  |  boolean;type  <data-lsp lsp="type T2 = string | boolean">T2</data-lsp>  =  string  |  boolean;type  <data-lsp lsp="type T3 = string | boolean" style="border-bottom:solid 2px lightgrey">T3</data-lsp>  =  <data-lsp lsp="type Extract<T, U> = T extends U ? T : never">Extract</data-lsp><<data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>,  <data-lsp lsp="type T2 = string | boolean">T2</data-lsp>>;` `type T3 = string | boolean`

```

typescript`type <data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp> =  number  |  string  |  boolean;type <data-lsp lsp="type T2 = string | boolean">T2</data-lsp> =  string  |  boolean;type <data-lsp lsp="type T3 = string | boolean" style="border-bottom:solid 2px lightgrey">T3</data-lsp> = <data-lsp lsp="type Extract<T, U> = T extends U ? T : never">Extract</data-lsp><<data-lsp lsp="type T1 = string | number | boolean">T1</data-lsp>, <data-lsp lsp="type T2 = string | boolean">T2</data-lsp>>;` `type T3 = string | boolean`

#### NonNullable

+   `NonNullable`は、nullまたはundefinedを含む型からいずれも除外するユーティリティ型。

```
typescript`type  <data-lsp lsp="type T1 = string | null | undefined">T1</data-lsp>  =  string  |  null  |  undefined;type  <data-lsp lsp="type T2 = string" style="border-bottom:solid 2px lightgrey">T2</data-lsp>  =  <data-lsp lsp="type NonNullable<T> = T &amp; {}">NonNullable</data-lsp><<data-lsp lsp="type T1 = string | null | undefined">T1</data-lsp>>;` `type T2 = string`

```

typescript`type <data-lsp lsp="type T1 = string | null | undefined">T1</data-lsp> =  string  |  null  |  undefined;type <data-lsp lsp="type T2 = string" style="border-bottom:solid 2px lightgrey">T2</data-lsp> = <data-lsp lsp="type NonNullable<T> = T &amp; {}">NonNullable</data-lsp><<data-lsp lsp="type T1 = string | null | undefined">T1</data-lsp>>;` `type T2 = string`

### Mapped types

+   Mapped typesを使うと、既存の型から新しい型を生成できる。

+   Mapped typesは、オブジェクトの各プロパティを”マップ”し、新しいオブジェクトを生成する。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type  <data-lsp lsp="type ReadOnlyPerson = {
    readonly name: string;
    readonly age: number;
}" style="border-bottom:solid 2px lightgrey">ReadOnlyPerson</data-lsp>  = { readonly [<data-lsp lsp="(type parameter) K">K</data-lsp>  in  keyof  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>]:  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>[<data-lsp lsp="(type parameter) K">K</data-lsp>] };` `type ReadOnlyPerson = {
    readonly name: string;
    readonly age: number;
}`

```

typescript`type <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type <data-lsp lsp="type ReadOnlyPerson = {

    readonly name: string;

    readonly age: number;

}" style="border-bottom:solid 2px lightgrey">ReadOnlyPerson</data-lsp> = { readonly [<data-lsp lsp="(type parameter) K">K</data-lsp> in  keyof <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp>]: <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp>[<data-lsp lsp="(type parameter) K">K</data-lsp>] };` `type ReadOnlyPerson = {

    readonly name: string;

    readonly age: number;

}`

### インデックスアクセス型を使うと、型のプロパティの型を取得できる。

+   Indexed Access Typesを使うと、型のプロパティの型を取得できる。

```
typescript`type  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type  <data-lsp lsp="type Name = string" style="border-bottom:solid 2px lightgrey">Name</data-lsp>  =  <data-lsp lsp="type Person = {
    name: string;
    age: number;
}">Person</data-lsp>["name"];` `type Name = string`

```

typescript`type <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp> = { <data-lsp lsp="(property) name: string">name</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number;};type <data-lsp lsp="type Name = string" style="border-bottom:solid 2px lightgrey">Name</data-lsp> = <data-lsp lsp="type Person = {

    name: string;

    age: number;

}">Person</data-lsp>["name"];` `type Name = string`

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```
