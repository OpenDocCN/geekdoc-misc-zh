# TypeScript 誕生の背景

> 原文：[`typescriptbook.jp/overview/before-typescript`](https://typescriptbook.jp/overview/before-typescript)

TypeScriptは、JavaScriptでも大規模なアプリケーションを開発しやすくすることを目的に開発されたプログラミング言語です。

確かにJavaScriptは元々、大規模な開発を想定した設計ではありませんでした。それでも、JavaScript 自体が進化して、大規模開発に対応してゆけば良かったはずです。しかし、実際はそううまくは行きませんでした。代わりに、大規模開発の一部はTypeScriptが引き受けることになったのです。

なぜ、そうなったのでしょうか？その答えはJavaScriptの歴史にあります。TypeScriptが必要な発明で、そして、今もなお必要とされている理由が見えてきます。それでは、TypeScript 誕生以前の歴史をひも解いていきましょう。

## 1990 年代​

### JavaScriptの誕生​

JavaScript 誕生以前は、簡単なフォームのバリデーションをするのも、サーバーサイドのプログラムで行う必要がありました。Netscape Navigatorというブラウザを開発していたNetscape 社は、クライアントサイドで動くプログラムの必要性に気���きました。そこで、1995 年、Netscape 社はNetscape Navigatorで動くスクリプト言語として、JavaScriptを実装しました。

### 補助的な道具​

当時のJavaScriptは、HTMLの補助的な言語と考えられていて、その用途は簡単なアニメーションを実装したり、フォームのバリデーションに使う程度でした。ましてや、JavaScriptが大規模なアプリケーションを作るための言語とは見なされていませんでした。

今となっては事実か不明ですが、当時 JavaScriptにはセキュリティ上の問題があるという主張があり、ブラウザの設定でJavaScriptをオフにした上でネットサーフィンをするのが、“ITリテラシーが高い人”という印象すらありました。そのため、サイトによっては「当サイトを閲覧するにはJavaScriptをオンにしてください」といった注意書きもしばしば見かけました。

1990 年代のJavaScriptは、現代のように必須のものでは決してなく、あくまで補助的・随意的な立ち位置の言語だったのです。

## 2000 年代初頭​

### くすぶりはじめる大規模開発のニーズ​

他のプラットフォームに目を移すと、この時期にはすでにブラウザアプリケーションを実現する技術として、[Javaアプレット](https://ja.wikipedia.org/wiki/Java%E3%82%A2%E3%83%97%E3%83%AC%E3%83%83%E3%83%88)や[Adobe Flash](https://ja.wikipedia.org/wiki/Adobe_Flash)がありました。特にFlashはJavaアプレットよりも動作が軽く、ウェブサイト全体をFlashで実装するサイトが登場したり、この時代を省みて「[Flash 黄金時代](https://dic.nicovideo.jp/a/flash%E9%BB%84%E9%87%91%E6%99%82%E4%BB%A3)」という言葉が後に生まれたりしました。一方のJavaScriptは依然として「補助的な道具」のイメージが支配的でした。

一般的に対話型のユーザーインターフェースを備えたウェブサイト、今で言うウェブアプリケーションは、当時は「リッチインターネットアプリケーション」と呼ばれ、その多くはJavaアプレットやFlashが担っていましたが、プログラマの中にはJavaScriptを使ったウェブアプリケーションの開発を試みる人たちもいました。

1997 年に、Microsoftが企業向けウェブメーラーとして、Outlook Web Access 2000を市場投入しましたが、これはJavaScript 製のウェブアプリケーションでした。現代の我々からすると意外かもしれませんが、この時代のJavaScriptはまだサーバーと通信することができませんでした。そこで、Microsoftはこのアプリのために、後のXMLHttpRequest(XHR)となるXMLHTTPという機能をInternet Explorerに追加したりもしました。XHRは革新的なアップデートでしたが、多くのプログラマから注目を得るのはもっと歴史が流れてからになります。

2000 年代初頭には、対話型のUIを備えた大規模なウェブアプリケーションがJavaScriptで開発できるようになることが望まれだしてきました。

### 失われた10 年​

この頃には、JavaScriptはNetscape 社が所有する言語から、ウェブ業界を上げて取り組む言語になっていました。そのため、JavaScriptの言語仕様はECMAScriptという名で策定され、各ベンダーがその仕様に基づいてそれぞれJavaScriptを実装するという流れになっていました。このECMAScriptを策定する会合がTC39であり、JavaScriptに関わるNetscape 社やMicrosoft 社を始めとしたベンダーが参加していました。

TC39では、大規模開発にも耐えうるJavaScriptの必要性を鑑みて、新たな言語仕様である「ECMAScript 4」の策定につ���ての議論を1999 年頃から始めていました。このECMAScript 4(ES4)では、主に次のような野心的な言語仕様が議論されていました:

+   モジュール

+   Javaのようなクラス

+   静的型付け

+   Nullable 型

+   ユニオン型

+   ジェネリクス

おや、どれもTypeScriptが持っているものではありませんか？そうなのです。「大規模なアプリケーション開発をしやすく」という点は、2つの言語が共有する問題意識であり、そのため、今から20 年前のJavaScriptにおいても、TypeScriptと同じような解決策が検討されていたのです。

ここでひとつ疑問が出てきます。「ES4のアイディアがJavaScriptにもたらされていたら、そもそもTypeScriptなんて必要なかったのでは？」という疑問です。

不幸的是，ES4 最终没有被采纳为正式规范。ES4 的规范制定经历了 2003 年的两年中断，2005 年重新启动，2007 年发布了规范草案。ES4 与之前的 JavaScript 不兼容。保守的微软和希望进行革新性改变的网景之间发生了分歧，由于政治背景的原因，ES4 的草案最终在 2008 年被废弃。

尽管 JavaScript 曾经致力于实现大规模化，但在未能实现这一目标的情况下，大约经过了 10 年的时间。

## 2000 年代中期​

### Google Map 的冲击​

在 JavaScript 的发展停滞不前、JavaScript 仍被视为不适合开发“真正的应用程序”的时候，网络行业发生了一件令人震惊的事件，那就是 2005 年 Google Map 的推出。

当时的许多地图网站在移动或缩放地图时都会重新加载页面，而 Google Map 可以在不刷新页面的情况下平滑操作地图，从当时的感觉来看，这是在网页上实现了类似原生应用程序的操作体验的划时代发明。

Google Map 背后支撑的是 AJAX。AJAX 是“**A**synchronous **Ja**vaScript and **X**ML”的缩写，利用 XMLHttpRequest 对象进行异步的 HTTP 通信，从服务器获取 XML 数据并在不刷新页面的情况下更新 HTML 的一部分。如今，AJAX 已经成为常识，甚至被视为过时技术，但在当时，它是最前沿的技术。

Google Map 给许多程序员带来了震撼。它不仅引领了 AJAX 的潮流，还证明了 JavaScript 也可以开发出优秀的应用程序。

## 2000 年代末​

### 大规模化的需求增强​

受 Google Map 的成功启发，开发者们开始更加热衷于提供无需安装其他任何内容的 Web 应用程序，只需浏览器即可使用，这进一步增加了对 JavaScript 大规模开发的需求。

2005 年，JavaScript 应用程序框架的先驱 Prototype.js 发布。次年，jQuery 发布，随后在 2009 年 AngularJS、2010 年 Backbone.js 相继问世，前端 Web 应用程序开发工具不断涌现。

### 无进化的 JS，一时风靡的 AltJS​

JavaScript 的开发风格发生了翻天覆地的变化，大规模化不断推进，但 JavaScript 本身并没有太多变化。曾经寄予厚望的 ES4 在 2008 年宣告失败。

开发者们并不甘心于停滞不前的 JavaScript。有人提出：“如果 JavaScript 本身无法改进，那么我们是否可以创造一种可以编译成 JavaScript 的语言？”这种想法开始在开发者中流行起来。

基于这种思路，2009 年推出的 CoffeeScript 风靡一时，成为 JavaScript 应用程序开发的语言。CoffeeScript 具有类似 Ruby 的简洁语法，被广泛接受，尤其受到熟悉面向对象编程的程序员的喜爱。

通过在其他语言中编写代码，然后将其编译成 JavaScript 的奇特方法取得了成功，采用这种方法的语言被称为 AltJS。将一种语言编译成另一种语言被称为“转译”，这个词也是在这个时期开始流行起来的。随着 AltJS 的普及，JavaScript 被戏称为“现代汇编语言”。

### ECMAScript 2015 的启动​

到了 2008 年，ECMAScript 出现了新的动向。人们重新开始讨论如何改进 JavaScript。由于 ES4 过于革新，遭到了保守派的强烈反对。因此，为了不像 ES4 那样过于革新，同时又能保持与现有 JS 的兼容性，提出了一个折衷方案，即新的语言规范 Harmony。Harmony 提出了类概念、模块概念、import/export 等面向大规模开发的语言规范。其中一些规范后来被采纳为 ECMAScript 2015 的一部分。

因此，讨论 JavaScript 语言规范的 TC39 会议变得更加富有成效，人们也开始对 JavaScript 的未来充满期待。

## 2010 年代​

### TypeScript 的诞生​

在 TC39 讨论大规模开发的热烈讨论中，2012 年推出了 TypeScript。

TypeScript 从诞生之初就专注于解决日益困难的 JavaScript 大规模开发问题。特别强调的特点包括 JavaScript 的超集、模块化以及类型。

当时，备受欢迎的 CoffeeScript 采取了与 JavaScript 语法截然不同的独特路线，而 TypeScript 则采用了扩展 JavaScript 语法的“JavaScript 超集语言”战略。因此，即使引入 TypeScript，现有的 JavaScript 资产也可以直接利用，团队学习也不会带来突发成本，逐渐增加 TypeScript 的好处，使其能够立即在大规模开发中使用。

在大规模开发中，模块化变得非常重要。如果没有能够将代码分割整理到适当粒度、封装实现细节、避免变量名和函数名冲突的语言规范，大规模开发将变得非常困难。

当时的 JavaScript 缺乏模块系统和命名空间等功能，导致大规模开发变得困难。为了解决这个问题，TypeScript 提前采用了 ES2015 中提出的类和模块语法，实现了模块化。

类型是 TypeScript 的最大特点。通过类型，编码过程中可以进行代码跳转和代码补全，类型信息也可以成为文档，使得在运行程序之前可以对源代码进行检查。因此，类型极大地提高了大规模开发的生产力。

### 不衰的 TypeScript 优势​

TypeScript 发布后，TypeScript 所借鉴的 ECMAScript 2015 正式发布，此后，ECMAScript 每年都会更新。曾一度停滞不前的 JavaScript 也在不断进化，以降低大规模开发的难度。

在这个过程中，TypeScript 最初提出的三大特点之一的模块性已经被纳入 JavaScript 规范中，因此在这一方面，TypeScript 失去了优势。然而，TypeScript 的“类型”仍然是其亮点，至今仍未被纳入 JavaScript 规范。

在进行大规模开发时，类型是非常重要的语言规范，即使在 JavaScript 不断发展的过程中，TypeScript 的“类型”仍然是其坚实的优势。

## 总结​

1995 年诞生的 JavaScript 最初并未考虑用于大规模开发。十年后，大规模开发的需求开始显现，JavaScript 不得不做出调整。然而，由于各方无法达成一致，JavaScript 的发展陷入停滞。

即使 JavaScript 处于停滞状态，Web 应用程序也在不断扩大规模，开发难度逐渐增加。对此，社区提出了各种解决方案。

TypeScript 就是在这样的背景下诞生的。作为一种面对大规模开发困难的语言，TypeScript 于 2012 年发布，具有 JavaScript 的超集、模块化和类型这三个特点。

TypeScript 的发布后，JavaScript 再次开始进步，6 年后发布了 ECMAScript 2015 作为重大更新，并从那时起每年发布新规范。然而，TypeScript 最大的特点“类型”在 JavaScript 中仍然不存在。直到今天，TypeScript 在大规模开发中受欢迎，是因为 JavaScript 无法提供的开发体验。

## 参考资料​

+   [第四章。JavaScript 的创造过程](http://speakingjs.com/es5/ch04.html)

+   [微软增强 JavaScript 以进行大规模开发 | InfoWorld](https://www.infoworld.com/article/2614863/microsoft-augments-javascript-for-large-scale-development.html)

+   [ECMAScript 背后的真实故事](https://auth0.com/blog/the-real-story-behind-es4/)

+   [JavaScript 2.0](https://web.archive.org/web/20000816194528/http://mozilla.org/js/language/js20-1999-02-18/index.html)

+   [JavaScript 2.0 动机](https://web.archive.org/web/20000823225602/http://mozilla.org/js/language/js20-1999-02-18/motivation.html)

+   [ActionScript - 维基百科](https://en.wikipedia.org/wiki/ActionScript)

+   [JavaScript - 维基百科](https://ja.wikipedia.org/wiki/JavaScript)

+   [ECMAScript - 维基百科](https://en.wikipedia.org/wiki/ECMAScript)

+   [JavaScript 简史](https://auth0.com/blog/a-brief-history-of-javascript/)

+   [ECMAScript 6 的时间表更改](https://2ality.com/2014/06/es6-schedule.html#fn2)

+   [看到的“ECMAScript 6”。JavaScript 之父撰写的“梦想成真的和谐” - Publickey](https://www.publickey1.jp/blog/12/javascriptecmascript_6harmony_of_dreams_come_true.html)

+   [JavaScript：前 20 年 | Zenod](https://zenodo.org/record/3707008#.XrVIhBMzZTY)

+   [Anders Hejlsberg: TypeScript 介绍 | Channel 9](https://channel9.msdn.com/posts/Anders-Hejlsberg-Introducing-TypeScript)
