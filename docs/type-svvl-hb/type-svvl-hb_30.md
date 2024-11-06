# シングルプロセス・シングルスレッドとコールバック

> 原文：[`typescriptbook.jp/reference/single-process-and-callback`](https://typescriptbook.jp/reference/single-process-and-callback)

コンピューティング。特に並列、並行処理をするプログラミングに入ってくるとプロセス、スレッドという言葉を耳にするようになります。

JavaScriptはシングルプロセス、シングルスレッドの言語です。これは言い換えるとすべてのプログラムは直列に処理されることを意味します。シングルスレッドの言語はコールスタックも1 個です。

コールスタックとは実行している関数の呼び出しの順序を司っているものです。スタックという言葉自体は関数の再帰呼び出しを誤って無限ループにしてしまった時に目にしたことがある人が多いのではないでしょうか。

```
ts`function  <data-lsp lsp="function stack(): never">stack</data-lsp>():  never {  <data-lsp lsp="function stack(): never">stack</data-lsp>();}<data-lsp lsp="function stack(): never">stack</data-lsp>();`
```

```
ts`function <data-lsp lsp="function stack(): never">stack</data-lsp>():  never { <data-lsp lsp="function stack(): never">stack</data-lsp>();}<data-lsp lsp="function stack(): never">stack</data-lsp>();`
```

```
text`RangeError: Maximum call stack size exceeded`
```

```
text`RangeError: Maximum call stack size exceeded`
```

## ブロッキング​

直列に処理されるということは、時間のかかる処理があるとその間は他の処理が実行されないことを意味します。

ブラウザでAJAX 通信を実装したことがある方は多いでしょう。AJAXはリクエストを送信してからレスポンスを受信するまでの間は待ち時間になりますが、直列で処理するのであればJavaScriptはこの間も他の処理ができないことになります。これをブロッキングと言います。

JavaScriptはブラウザで発生するクリック、各種 input 要素からの入力、ブラウザの履歴の戻る進むなど、各種イベントをハンドリングできる言語ですが、時間のかかる処理が実行されている間はブロッキングが起こるためこれらの操作をハンドリングできなくなります。画面の描画もJavaScriptに任せていた場合はさらに画面が止まっ���ように見えるでしょう。

```
ts`<data-lsp lsp="function ajax(url: string): Promise<unknown>">ajax</data-lsp>("https://...");<data-lsp lsp="function wait(ms: number): Promise<void>">wait</data-lsp>(3000);if (!<data-lsp lsp="function ajaxDone(): boolean">ajaxDone</data-lsp>()) {  <data-lsp lsp="function cancelAjax(): Promise<void>">cancelAjax</data-lsp>();}`
```

```
ts`<data-lsp lsp="function ajax(url: string): Promise<unknown>">ajax</data-lsp>("https://...");<data-lsp lsp="function wait(ms: number): Promise<void>">wait</data-lsp>(3000);if (!<data-lsp lsp="function ajaxDone(): boolean">ajaxDone</data-lsp>()) { <data-lsp lsp="function cancelAjax(): Promise<void>">cancelAjax</data-lsp>();}`
```

上記のメソッドたちはどれも実在するメソッドではありませんが、おおよその意味を理解していただければ問題ありません。これを先入観なく見ると

1.  AJAXを開始する

1.  3000ms 待つ

1.  AJAXが終わっていなかったら

    1.  AJAXを中止する

のように見えるかもしれませんが、これはその意図した動作にはなりません。実際には次のようになります。

1.  AJAXをして、結果を取得する（ブロックして戻ってきたら2に進む)

1.  3000ms 待つ

1.  AJAXが終わっていなかったら(すでに終了している)

1.  AJAXを中止する

となります。もちろん`ajaxDone()`は`ajax()`の時点で結果にかかわらず終了しているため`cancelAjax()`は実行されません。

## ノンブロッキング​

ブロッキングの逆の概念です。Node.jsはノンブロッキングI/Oを取り扱うことができます。

これは入出力の処理が終わるまで待たずにすぐに呼び出し元に結果を返し、追って別の方法で結果を伝える方式を指します。

ここで指している入出力とはアプリケーションが動くマシン(サーバー)が主にリポジトリと呼ばれるようなファイル、リクエスト、DBなど他のデータがある場所へのアクセスを指す時に使われます。

ノンブロッキングかわかりやすい例としては次のようなものがあります。

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("first");<data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("second");},  1000);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("third");`
```

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("first");<data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("second");},  1000);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("third");`
```

`setTimeout()`は実際に存在する関数です。第 2 引数では指定したミリ秒後に第 1 引数の関数を実行します。ここでは1000を指定しているので、1000ミリ秒、つまり1 秒後となります。

JavaScriptを始めて日が浅い方はこのコードに対する出力を次のように考えます。

```
text`firstsecondthird`
```

```
text`firstsecondthird`
```

実際の出力は以下です。

```
text`firstthirdsecond`
```

```
text`firstthirdsecond`
```

`setTimeout()`がノンブロッキングな関数です。この関数は実行されると第 1 引数の関数をいったん保留し、処理を終えます。そのため次の`console.log('third')`が実行され、1000ミリ秒後に第 1 引数の関数が実行され、中にある`console.log('second')`が実行されます。

1000ミリ秒は待ちすぎ、もっと短ければ意図する順番通りに表示される。と思われるかもしれませんが、基本的に意図するとおりにはなりません。以下は第 2 引数を1000ミリ秒から0ミリ秒に変更した例ですが、出力される内容は変更前と変わりません。

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("first");<data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("second");},  0);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("third");'first''third''second'`
```

```
ts`<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("first");<data-lsp lsp="function setTimeout<[]>(callback: () => void, ms?: number | undefined): NodeJS.Timeout (+2 overloads)
namespace setTimeout">setTimeout</data-lsp>(() => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("second");},  0);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("third");'first''third''second'`
```

現実世界の料理に例えてみるとわかりやすいかもしれません。お米を炊いている40 分間、ずっと炊飯器の前で待機する料理人はおらず、その間に別のおかずを作るでしょう。

時間はかかるものの待機が多い作業、炊飯器なら炊飯ボタンを押したら炊き上がるまでの間待たずに他の処理の実行に移ることがノンブロッキングを意味します。

## ノンブロッキングを成し遂げるための立役者​

ノンブロッキングを語る上で欠かせない、必ず目にすることになるであろう縁の下の力持ちを紹介します。

### メッセージキュー​

メッセージキューとはユーザーからのイベントや、ブラウザからのイベントなどを一時的に蓄えておく領域です。メッセージキューに蓄積されたイベントはコールスタックが空のときにひとつずつコールスタックに戻されます。

### コールバック​

`setTimeout()`のときに説明した**いったん保留した関数**は、いわゆるコールバック関数と呼ばれます。前項で述べた、**追って別の方法で伝える**というのは、このコールバック関数のことです。

コールバック関数は、ある関数が条件を満たした時、前項の例だと1000ミリ秒後に、メッセージキューに蓄積されます。メッセージキューに蓄積されるだけなので、実際に実行されるのはコールスタックが空になるまでさらに時間がかかります。

いままで`setTimeout()`は第 2 引数のミリ秒だけ遅延させてコールバック関数を実行すると説明していましたが、厳密にはミリ秒経過後にメッセージキューに戻すだけで、そのコールバック関数が即座に実行されるわけではありません。

### イベントループ​

イベントループは単純な無限ループです。常にコールスタックを監視しており、イベントがあればそれを実行します。普通の関数呼び出しのスタック以外にもメッセージキューが戻してきたイベントも処理します。現時点では詳しくは説明しませんが、ずっとイベントをどうにかしてくれているやつがいるなー、程度の認識でオッケーです！

## ノンブロッキングの弊害​

ノンブロッキングにはたくさんいいところがあって頼れる仲間ですが、そのノンブロッキングが時として唐突に牙を剥くことがあります。こわいですねぇ。

### 回调地狱（Callback hell）​

回调地狱中的**负面产物**。

一般情况下，回调函数用于接收需要一定时间才能完成的处理结果。采用回调函数的函数主要具有以下形式。

```
ts`function  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>(<data-lsp lsp="(parameter) uri: string">uri</data-lsp>:  string,  <data-lsp lsp="(parameter) callback: (res: Response) => void">callback</data-lsp>: (<data-lsp lsp="(parameter) res: Response">res</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) =>  void):  void {  // ...}`
```

```
ts`function <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>(<data-lsp lsp="(parameter) uri: string">uri</data-lsp>:  string, <data-lsp lsp="(parameter) callback: (res: Response) => void">callback</data-lsp>: (<data-lsp lsp="(parameter) res: Response">res</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) =>  void):  void {  // ...}`
```

在使用这个函数时，会是这样的。

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res: Response">res</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ...});`
```

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res: Response">res</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ...});`
```

在这里，如果想要接收这个函数`ajax()`的结果并进一步使用`ajax()`，就会变成这样。

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res1: Response">res1</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res2: Response">res2</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ... });});`
```

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res1: Response">res1</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res2: Response">res2</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ... });});`
```

缩进（嵌套）会变得很深。如果这种情况反复出现，就会变得难以忍受。

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res1: Response">res1</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res2: Response">res2</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res3: Response">res3</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res4: Response">res4</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res5: Response">res5</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res6: Response">res6</data-lsp>:  <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ... }); }); }); }); });});`
```

```
ts`<data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res1: Response">res1</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res2: Response">res2</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res3: Response">res3</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res4: Response">res4</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res5: Response">res5</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => { <data-lsp lsp="function ajax(uri: string, callback: (res: Response) => void): void">ajax</data-lsp>("https://...", (<data-lsp lsp="(parameter) res6: Response">res6</data-lsp>: <data-lsp lsp="interface Response">Response</data-lsp>) => {  // ... }); }); }); }); });});`
```

作为解决这种回调地狱的划时代类的`Promise`出现了，在主要的浏览器和 Node.js 中可以作为内置对象使用。关于这个功能的说明，本书有专门的页面，请参考那里。

## 📄️ 异步处理

如果想要在 JavaScript 中真正地构建一些东西，那么与异步处理将会有密不可分的关系。一开始可能会很难理解，但现在已经实现了可以直观操作异步处理的功能，因此门槛大大降低了。
