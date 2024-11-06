# Jestでテストを書こう

> 原文：[`typescriptbook.jp/tutorials/jest`](https://typescriptbook.jp/tutorials/jest)

このチュートリアルでは、テストフレームワーク「Jest」を使い、ユニットテストをTypeScriptで書くことを学びます。

## 本章で学べること​

本章では、簡単な関数のテストをJestで書くことを目標に、次のことを学びます。

+   Jestを使ってTypeScriptの関数をテストする方法

+   Jestの導入方法

+   Jestでのテストの書き方

+   テストの実行方法

+   結果の見方

本章の目的はJestを完全に理解することではありません。むしろ、Jestがどういったものなのか、その雰囲気を実際に体験することに主眼を置いています。そのため、内容はかなり最低限のものとなりますが、逆に言えば少しの時間でJestを試してみれるシンプルな内容にまとまってますから、ぜひ手を動かしてみてください。

## Jestとは​

JestはJavaScriptのテストフレームワークです。TypeScriptでテストを書くこともできます。Jestは、フロントエンドライブラリのReactやVueなどのテストだけでなく、Node.js 向けのパッケージのテストも行えます。要するに、JavaScriptやTypeScriptで書かれたコードであれば、そのほとんどはJestでテストが行えます。

## この���ュートリアルに��要なもの​

このチュートリアルで必要なものは次のとおりです。

+   Node.js v16 以上

+   Yarn v1 系 (このチュートリアルはv1.22.19で動作確認しています)

Node.jsの導入については、開発環境の準備をご覧ください。

パッケージ管理ツールとしてYarnを利用します。最初にインストールをしておきましょう。すでにインストール済みの方はここのステップはスキップして大丈夫です。

```
shell`npm install -g yarn`
```

```
shell`npm install -g yarn`
```

## プロジェクトを作成する​

まず、このチュートリアルに使うプロジェクトを作成します。

```
shell`mkdir jest-tutorialcd jest-tutorial`
```

```
shell`mkdir jest-tutorialcd jest-tutorial`
```

プロジェクトルートにpackage.jsonを作ってください。

```
shell`touch package.json`
```

```
shell`touch package.json`
```

package.jsonの内容は次のようにします。

```
package.jsonjson`{  "name":  "jest-tutorial",  "license":  "UNLICENSED"}`
```

```
package.jsonjson`{  "name":  "jest-tutorial",  "license":  "UNLICENSED"}`
```

## TypeScriptのインストール​

プロジェクトにTypeScriptをインストールします。

```
shell`yarn add -D typescript`
```

```
shell`yarn add -D typescript`
```

次に、tsconfig.jsonを生成します。

```
shell`yarn tsc --init`
```

```
shell`yarn tsc --init`
```

## Jestをインストールする​

Jestをプロジェクトにインストールしましょう。インストールが必要なパッケージは、次の3つです。

1.  jest

1.  ts-jest

1.  @types/jest

これらのインストールは次のコマンドで、一度にインストールできます。

```
shell`yarn add -D 'jest@²⁸.0.0'  'ts-jest@²⁸.0.0'  '@types/jest@²⁸.0.0'`
```

```
shell`yarn add -D 'jest@²⁸.0.0'  'ts-jest@²⁸.0.0'  '@types/jest@²⁸.0.0'`
```

`jest`はJest 本体です。JavaScriptだけのプロジェクトであれば、このパッケージを入れるだけでテストが始められます。`ts-jest`は、JestをTypeScriptに対応させるためのものです。`ts-jest`を入れると、TypeScriptで書いたテストコードを、コンパイルの手間なしにそのまま実行できるようになります。`@types/jest`はJestのAPIの型定義ファイルです。TypeScriptの型情報を付与されるので、テストコードの型チェックが行えるようになります。

## Jestの設定ファイルを作る​

JestはそのままではTypeScriptを直接テストできません。なので、ここではJestでTypeScriptコードがテストできるように設定を加えます。

次のコマンドを実行すると、Jestの設定ファイル`jest.config.js`が生成されます。

```
shell`yarn ts-jest config:init`
```

```
shell`yarn ts-jest config:init`
```

生成された`jest.config.js`の内容は次のようになります。

```
jest.config.jsts`/** @type  {import("ts-jest/dist/types").InitialOptionsTsJest} */<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  = { <data-lsp lsp="(property) preset: string">preset</data-lsp>:  "ts-jest", <data-lsp lsp="(property) testEnvironment: string">testEnvironment</data-lsp>:  "node",};`
```

```
jest.config.jsts`/** @type  {import("ts-jest/dist/types").InitialOptionsTsJest} */<data-lsp lsp="var module: NodeModule">module</data-lsp>.<data-lsp lsp="(property) NodeJS.Module.exports: any">exports</data-lsp>  = { <data-lsp lsp="(property) preset: string">preset</data-lsp>:  "ts-jest", <data-lsp lsp="(property) testEnvironment: string">testEnvironment</data-lsp>:  "node",};`
```

この`@type`のコメントはエディターに型情報を与えるためのものです。これを書いておくことで、エディター上で入力補完が効くようになります。

## チェックポイント​

ここまでに作成したファイルに漏れがないか確認しましょう。

```
text`├── jest.config.js ... Jestの設定ファイル├── node_modules ... jestやtypescriptがインストールされたフォルダ├── package.json├── tsconfig.json ... TypeScriptの設定ファイル└── yarn.lock`
```

```
text`├── jest.config.js ... Jestの設定ファイル├── node_modules ... jestやtypescriptがインストールされたフォルダ├── package.json├── tsconfig.json ... TypeScriptの設定ファイル└── yarn.lock`
```

## Jestが動くかを確認する​

ここでは、実際のテストコードを書く前に、Jestでテストコードが実行できる状態になっているかを、動作確認用のテストファイルを作って確かめます。

Jestで実行できるテストファイルには命名規則があります。ファイル名が`.test.ts`または`.spec.ts`で終わるものが、テストファイルになります。動作確認用のファイルとして、`check.test.ts`を作ってください。

```
shell`touch check.test.ts`
```

```
shell`touch check.test.ts`
```

`check.test.ts`の内容は次のようにします。

```
check.test.tsts`<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("check", () => {  <data-lsp lsp="var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(...data: any[]): void">log</data-lsp>("OK");});`
```

```
check.test.tsts`<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("check", () => {  <data-lsp lsp="var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(...data: any[]): void">log</data-lsp>("OK");});`
```

ファイルを保存したら、`jest`コマンドを実行してみてください。

```
shell`yarn jest`
```

```
shell`yarn jest`
```

すると、次のような結果が出るはずです。

![](img/bdac84b6f7355986c11b24f13383ca70.png)

結果に`check.test.ts`が「PASS」と表示されていれば、テストファイルが実行されていることになります。

問題なく実行されていることが確認できたら、`check.test.ts`は削除してください。

```
削除するコマンドshell`rm check.test.ts`
```

```
削除するコマンドshell`rm check.test.ts`
```

## このチュートリアルでテストする関数​

ここからは、TypeScriptのテスト対象コードを書いて、それをテストしていきます。

具体的には、次のような簡単な関数のテストを書くことを例に進めていきます。

```
ts`function  <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}`
```

```
ts`function <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}`
```

この`isZero`関数は、数値がゼロかどうかを判定するものです。

## テスト対象のファイルを作る​

まず、この関数を書いたファイルを作ります。ファイル名は`isZero.ts`にしてください。

```
shell`touch isZero.ts`
```

```
shell`touch isZero.ts`
```

このファイルを作ると、プロジェクトのファイル構成は次のようになります。

```
text`├── isZero.ts ... テスト対象ファイル├── jest.config.js├── node_modules├── package.json├── tsconfig.json└── yarn.lock`
```

```
text`├── isZero.ts ... テスト対象ファイル├── jest.config.js├── node_modules├── package.json├── tsconfig.json└── yarn.lock`
```

`isZero.ts`の内容は次のようにします。

```
isZero.tsts`function  <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}// 注意: このままではテストできません。`
```

```
isZero.tsts`function <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}// 注意: このままではテストできません。`
```

このままでは`isZero`関数はテストできません。Jestでテストできるようにするには、関数をエクスポートする必要があります。関数をエクポートするために、`function`の前に`export`キーワードを追加してください。

```
isZero.tsts`export  function  <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}`
```

```
isZero.tsts`export  function <data-lsp lsp="function isZero(value: number): boolean">isZero</data-lsp>(<data-lsp lsp="(parameter) value: number">value</data-lsp>:  number):  boolean {  return <data-lsp lsp="(parameter) value: number">value</data-lsp> ===  0;}`
```

## テストコードを書く​

上の`isZero`関数をテストするコードを書きます。

Jestではテストコードはテスト対象と別のファイルに書きます。テストファイルを作りましょう。ファイル名は、テストしたいファイル名に、`.test.ts`をつけたものにします。テスト対象ファイルが`isZero.ts`なので、ここでは`isZero.test.ts`というファイル名��します。

```
shell`touch isZero.test.ts`
```

```
shell`touch isZero.test.ts`
```

このファイルを作ると、プロジェクトのファイル構成は次のようになります。

```
text`├── isZero.ts ... テスト対象ファイル├── isZero.test.ts ... テストコードのファイル├── jest.config.js├── node_modules├── package.json├── tsconfig.json└── yarn.lock`
```

```
text`├── isZero.ts ... テスト対象ファイル├── isZero.test.ts ... テストコードのファイル├── jest.config.js├── node_modules├── package.json├── tsconfig.json└── yarn.lock`
```

テスト対象の関数をテストコードで扱うには、まず関数をインポートする必要があります。`import`文を使って、`isZero`関数を読み込みましょう。

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";`
```

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";`
```

次に、1つ目のテストケースを追加します。このテストケースは、`isZero`関数に`0`を渡したら`true`が返るかをチェックするものです。

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("0を渡したらtrueになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  =  <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(0);  <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(true);});`
```

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("0を渡したらtrueになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  = <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(0); <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(true);});`
```

Jestでは`expect`関数とマッチャーを使い、結果が期待する値になっているかを記述します。マッチャーは、`expect`関数の戻り値に生えているメソッドです。上の例では、`toBe`がマッチャーになります。このメソッドの引数には期待値を書きます。上のテストケースでは、`true`が期待値なので、`toBe(true)`と記述しています。

`toBe`マッチャーは、JavaScriptの厳密等価比較(`===`)と同じです。したがって、`expect(result).toBe(true)`は内部的に`result === true`かを評価します。もし、この評価が真なら、テストは合格します。逆に、偽ならテストは不合格となります。

マッチャーは、`toBe`以外にもさまざまなものがあります。このチュートリアルでは細かく解説しないので、詳しく知りたい方は、[公式ドキュメントのリファレンス](https://jestjs.io/ja/docs/expect)をご覧ください。

## テストを実行する​

1つ目のテストケースができたので、Jestでテストを実行してみましょう。

```
shell`yarn jest`
```

```
shell`yarn jest`
```

テスト結果は次のように表示されていれば、テストの実行ができています。

![](img/3d3089db01fb51193bdfd98b3c188715.png)

## テストケースを追加する​

さらにテストケースを追加してみましょう。今度は、`isZero`関数に`1`を渡して、戻り値が`false`になるかをチェックするケースを追加します。

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("0を渡したらtrueになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  =  <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(0);  <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(true);});<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("1を渡したらfalseになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  =  <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(1);  <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(false);});`
```

```
isZero.test.tsts`import { <data-lsp lsp="(alias) function isZero(value: number): boolean
import isZero">isZero</data-lsp> } from  "./isZero";<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("0を渡したらtrueになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  = <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(0); <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(true);});<data-lsp lsp="var test: jest.It
(name: string, fn?: jest.ProvidesCallback | undefined, timeout?: number | undefined) => void">test</data-lsp>("1を渡したらfalseになること", () => {  const  <data-lsp lsp="const result: boolean">result</data-lsp>  = <data-lsp lsp="(alias) isZero(value: number): boolean
import isZero">isZero</data-lsp>(1); <data-lsp lsp="const expect: jest.Expect
<boolean>(actual: boolean) => jest.JestMatchers<boolean>">expect</data-lsp>(<data-lsp lsp="const result: boolean">result</data-lsp>).<data-lsp lsp="(method) jest.Matchers<void, boolean>.toBe<boolean>(expected: boolean): void">toBe</data-lsp>(false);});`
```

テストケースを追加したら、再びJestを実行し、テストコードを走らせます。

```
shell`yarn jest`
```

```
shell`yarn jest`
```

今度は次のような結果になるはずです。

![](img/d865a436ba77eb45bb9a482e619de710.png)

以上でJestを体験してみるチュートリアルは完了です。
