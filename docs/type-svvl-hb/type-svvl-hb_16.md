# 簡単な関数を作ってみよう

> 原文：[`typescriptbook.jp/tutorials/make-a-simple-function-via-cli`](https://typescriptbook.jp/tutorials/make-a-simple-function-via-cli)

このチュートリアルではTypeScriptで簡単な関数を作る体験を通じて、TypeScriptの型がJavaScriptのどのような問題を解決するのか、コンパイラはどのような役割を果たすのかを学びます。

## このチュートリアルに必要なもの​

このチュートリアルをやるに当たり、必要なツールがあります。次にリストアップするものを準備しておいてください。

+   Node.js

+   VS CodeやWebStormなどのエディター

+   tsc(TypeScriptコンパイラ)

## 📄️ 開発環境の準備

TypeScriptの開発に必要になるNode.jsとTypeScriptコンパイラ、エディタをインストールしましょう。

## JavaScriptで発生しうる問題​

まず、次のJavaScriptファイルをローカル環境に作ります。

```
increment.jsjs`function  increment(num) {  return num +  1;}``console.log(increment(999));`

```

increment.jsjs`function increment(num) {  return num +  1;}``console.log(increment(999));`

このプログラムは引数をインクリメントして返すだけのものです。これをNode.jsで実行してみましょう。

```
sh`$ node increment.js1000`
```

```
sh`$ node increment.js1000`
```

問題なく動いたと思います。つづいて、`increment`関数の引数を`999`からstring 型の`"999"`に書き換えてみましょう。

```
increment.jsjs`function  increment(num) {  return num +  1;}``console.log(increment("999"));//                    ^^^^^`

```

increment.jsjs`function increment(num) {  return num +  1;}``console.log(increment("999"));//                    ^^^^^`

この小さな変更で実行結果は大きく変わってしまいます。実行してみましょう。

```
sh`$ node increment.js9991`
```

```
sh`$ node increment.js9991`
```

出力結果は1000から9991に変わったはずです。この理由は、引数`num`が文字列になったせいで、`+`演算子が足し算ではなく文字列結合になったからです。JavaScriptは`"999" + 1`を`"999" + "1"`と解釈します。この解釈の詳細を知るには型強制の説明をご覧ください。

## 📄️ 型強制

JavaScriptにはデータ型がありますが、型が異なる2つの値に対し演算してもエラーにならない場合があります。たとえば、string 型の"1"からnumber 型の1を減算した場合、number 型の0が計算結果として出てきます。

引数は`999`と`"999"`という型の微妙な違いだけです。もしもこれが金額の計算だったら大問題です。`increment`関数は引数`num`がnumber 型のときだけ正しい動きをします。しかし、関数を呼び出すときは、制約なしにさまざまな型を渡せてしまいます。引数にnumber 型のみ代入できるように制約するには、どのようにしたらよいのでしょうか。ここでTypeScriptの出番になります。

## JavaScriptをTypeScriptに変換する​

JavaScriptをTypeScriptにする第一歩は、ファイルの拡張子を`.js`から`.ts`に変更することです。TypeScriptはざっくり言って、JavaScriptに型関連の構文を追加したにすぎない言語です。なので、JavaScriptのコードはそのままでもTypeScriptとして扱えます。

```
sh`mv increment.js increment.ts`
```

```
sh`mv increment.js increment.ts`
```

## コンパイラを働かせる​

TypeScriptの目玉機能はなんと言ってもコンパイラです。コンパイラの役割のひとつは、上例のような型の問題をチェックし、発見した���題点をプログラマに報告することです。TypeScriptコンパイラはとても賢く、ノーヒントでも型の問題を指摘してくれます。しかし、ヒントを十分に与えたほうが、コンパイラはもっと緻密なチェックをしてくれます。

コンパイラに与えるヒントのことを「型注釈(type annotation)」と言います。それでは、`increment`関数の引数`num`に型注釈を書いてみましょう。型注釈は`num`の右に`: number`と書きます。これを書くことで「引数`num`はnumber 型だけが代入できます」という意味になります。コンパイラはこれをヒントに関数呼び出しコードをチェックするようになります。

```
increment.tsts`function  <data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number) {//                 ^^^^^^^^型注釈  return <data-lsp lsp="(parameter) num: number">num</data-lsp> +  1;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>("999"));`
```

```
increment.tsts`function <data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number) {//                 ^^^^^^^^型注釈  return <data-lsp lsp="(parameter) num: number">num</data-lsp> +  1;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>("999"));`
```

型注釈を書いたら、TypeScriptコンパイラにチェックをさせてみましょう。TypeScriptコンパイラのコマンドは`tsc`です。

```
sh`tsc increment.ts`
```

```
sh`tsc increment.ts`
```

すると、次のエラーが報告されるはずです。

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-err>"999"</data-err>));Argument of type 'string' is not assignable to parameter of type 'number'.2345Argument of type 'string' is not assignable to parameter of type 'number'.`
```

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-err>"999"</data-err>));Argument of type 'string' is not assignable to parameter of type 'number'.2345Argument of type 'string' is not assignable to parameter of type 'number'.`
```

このエラーの内容は、「引数`num`はnumber 型しか代入できないはずだが、関数呼び出しではstring 型を代入している。本当に問題ないか？」という指摘です。

エラーというと望まれないものというイメージがあるかもしれません。しかし、コンパイラが報告するエラーはむしろ歓迎されるものです。なぜなら、自分の代わりにコードに潜んでいる危険を、コーディング時点で知らせてくれるからです。

## コンパイルを通す​

コンパイラが指摘する問題点をすべて解消する作業のことを「コンパイルを通す」といいます。上のコードをコンパイルが通るコードに直してみましょう。直し方は単純に、関数呼び出しの引数をnumber 型にするだけです。

```
increment.tsts`function  <data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number) {  return <data-lsp lsp="(parameter) num: number">num</data-lsp> +  1;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>(999));//                    ^^^直す箇所`
```

```
increment.tsts`function <data-lsp lsp="function increment(num: number): number">increment</data-lsp>(<data-lsp lsp="(parameter) num: number">num</data-lsp>:  number) {  return <data-lsp lsp="(parameter) num: number">num</data-lsp> +  1;}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="function increment(num: number): number">increment</data-lsp>(999));//                    ^^^直す箇所`
```

直したら再びコンパイルしてみましょう。

```
sh`tsc increment.ts`
```

```
sh`tsc increment.ts`
```

今度は何も表示されずに処理が終わるはずです。コンパイル成功です。

## 生成されたJavaScript​

ここまでの手順で、increment.jsというファイルができていることに気づいたかもしれません。そのファイルの内容は次のようになっていると思います。

```
increment.jsts`function  increment(num) {  return num +  1;}console.log(increment(999));`
```

```
increment.jsts`function increment(num) {  return num +  1;}console.log(increment(999));`
```

これは、increment.tsをコンパイルする過程でコンパイラが生成したJavaScriptファイルです。TypeScriptのコードと比べてみると、引数`num`から型注釈が取り除かれていることがわかります。

型注釈の部分はTypeScript 固有のものです。それが書いてあるとブラウザやNode.jsでは実行できません。なので、TypeScriptコンパイラはJavaScript 実行環境で動かす用のJavaScriptファイルを生成してくれます。開発者はこの成果物のJavaScriptファイルを本番環境にデプロイすることになります。

##### 学びをシェアする

・JavaScriptからTypeScriptへの書き換えは拡張子を.tsにする

・コンパイラは型の問題を教えてくれる

・型注釈を書き加えると、コンパイラはより細かいチェックをしてくれる

・コンパイラが生成したJSをデプロイして使う

『サバイバルTypeScript』より

[この内容をツイートする](https://twitter.com/intent/tweet?text=%E3%83%BBJavaScript%E3%81%8B%E3%82%89TypeScript%E3%81%B8%E3%81%AE%E6%9B%B8%E3%81%8D%E6%8F%9B%E3%81%88%E3%81%AF%E6%8B%A1%E5%BC%B5%E5%AD%90%E3%82%92.ts%E3%81%AB%E3%81%99%E3%82%8B%0A%E3%83%BB%E3%82%B3%E3%83%B3%E3%83%91%E3%82%A4%E3%83%A9%E3%81%AF%E5%9E%8B%E3%81%AE%E5%95%8F%E9%A1%8C%E3%82%92%E6%95%99%E3%81%88%E3%81%A6%E3%81%8F%E3%82%8C%E3%82%8B%0A%E3%83%BB%E5%9E%8B%E6%B3%A8%E9%87%88%E3%82%92%E6%9B%B8%E3%81%8D%E5%8A%A0%E3%81%88%E3%82%8B%E3%81%A8%E3%80%81%E3%82%B3%E3%83%B3%E3%83%91%E3%82%A4%E3%83%A9%E3%81%AF%E3%82%88%E3%82%8A%E7%B4%B0%E3%81%8B%E3%81%84%E3%83%81%E3%82%A7%E3%83%83%E3%82%AF%E3%82%92%E3%81%97%E3%81%A6%E3%81%8F%E3%82%8C%E3%82%8B%0A%E3%83%BB%E3%82%B3%E3%83%B3%E3%83%91%E3%82%A4%E3%83%A9%E3%81%8C%E7%94%9F%E6%88%90%E3%81%97%E3%81%9FJS%E3%82%92%E3%83%87%E3%83%97%E3%83%AD%E3%82%A4%E3%81%97%E3%81%A6%E4%BD%BF%E3%81%86%0A%0A%E3%80%8E%E3%82%B5%E3%83%90%E3%82%A4%E3%83%90%E3%83%ABTypeScript%E3%80%8F%E3%82%88%E3%82%8A

```

```

```

```
