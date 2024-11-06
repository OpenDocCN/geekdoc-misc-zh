# なぜTypeScriptを使うべきか

> 原文：[`typescriptbook.jp/overview/why-you-should-use-typescript`](https://typescriptbook.jp/overview/why-you-should-use-typescript)

ウェブアプリケーションのフロントエンドを開発するのに、最低限の必要となる言語はHTMLやCSSを除けばJavaScriptだけです。JavaScriptさえ使えれば、かなり自由にフロントエンドを実装できます。それなのに、なぜJavaScriptではなくTypeScriptを使ったほうがいいのでしょうか？ここでは、TypeScriptを使うべき理由を大きく分けて4つ見ていきます。

## TypeScriptは大規模開発に最適な言語​

TypeScriptが発明されるに至った歴史的背景を「TypeScript 誕生の背景」で見ましたが、JavaScriptではまかないきれなくなった大規模アプリケーション開発を克服するために生まれたのがTypeScriptです。

## 📄️ TypeScript 誕生の背景

TypeScriptは、JavaScriptでも大規模なアプリケーションを開発しやすくすることを目的に開発されたプログラミング言語です。

そのため、大規模なアプリケーション開発の現場が求める三大特徴をTypeScriptは備えています。

1.  型による静的チェック

1.  モジュール性

1.  緩やかな学習コスト

このうち特に型による静的チェックは、TypeScriptに「Type」という名が冠されているように、TypeScriptの目玉機能です。型チェックはプログラムを実行せずとも、プログラムの欠陥に気づくことができます。バグは発見が遅れるほど修正コストが高くつきますが、TypeScriptではコーディング中に頻繁にチェックすることができ、バグ早期発見によって修正コストも抑えることができます。Airbnbによると、[TypeScriptを使っていたらAirbnbの38%ものバグを未然に防げたと見る分析](https://www.reddit.com/r/typescript/comments/aofcik/38_of_bugs_at_airbnb_could_have_been_prevented_by/)を発表しています。

また、型があることで、プログラムの可読性や理解しやすさが上がったり、エディターの補完機能を活かすことができ、コーディングの効率も良くなります。

TypeScriptは公式に「大規模なアプリケーション」が具体的にどれほどの規模なのかは明言していませんが、筆者の感覚からいうと、数百行規模のコードでもTypeScriptの恩恵は十分に享受できると考えています。

ただし、静的チェックは品質保証の銀の弾丸ではないことは、公平に申しておかなければなりません。静的チェックは、誰が読んでも絶対におかしいと客観的に判断できるような欠陥をあぶり出すものです。たとえば、未定義の変数へのアクセスや、正しくないデータ型の取り扱いなどです。仕様バグや、実行時エラーを検出することはできません。品質保証においては、テストなど他の手法も組み合わせる必要があります。それでも、静的チェックがあるおかげで、TypeScriptで検出できる類のバグはテスト工程から省略できるのは確かです。

## JavaScriptの知識があれば使い始められる​

TypeScriptはJavaScriptのスーパーセットです。スーパーセットというのは、JavaScriptの仕様はそのままに、それにTypeScriptならではの新しい機能や利点を追加したものという意味です。つまり、JavaScriptのコードはそのままTypeScriptのコンパイラが理解できるのです。

この特徴により、開発陣が得られるメリットのひとつが、JavaScriptの知識があればTypeScriptを使い始められるということです。これは新しい言語の学習コストをとても緩やかなものにしてくれます。新言語の導入となると、難しい言語だと学習に数ヶ月要し、そこからやっと書きはじめるということもありえますが、TypeScriptの場合はひとまずJavaScriptとして書き始め、少しずつTypeScriptを学んでいき、徐々にTypeScriptの恩恵を最大化するようにコードを手直ししていくといったアプローチが可能です。TypeScriptにはJavaScriptにはない数多くの機能がありますが、どれも選択的に導入していくことができます。

JavaScriptのスーパーセットであるということは、裏を返せばJavaScriptを知らないといけないということでもあります。なので、TypeScriptをJavaやC#のようなものだと期待していたり、JavaScriptを学ぶつもりがまったくないとすると、TypeScriptでの開発はフラストレーションになるかもしれません。JavaScriptでいわゆる「罠」と言われるような注意すべき言語仕様は、TypeScriptでもそのままというものもあります。JavaScriptにまったく触れたくないならTypeScriptは適していませんが、JavaScriptを使うつもりでいたのならTypeScriptは有力な選択肢になるでしょう。

## 古いJS 環境を対象とした開発シーンでも最新の構文が使える​

プロジェクトの要件によっては、ES5といった古いJavaScriptしかサポートされていないブラウザでも動作するように実装しないといけない場合があります。TypeScriptは、そのような古いJS 環境をターゲットとしたプロジェクトにも導入可能です。

TypeScriptはコンパイル時にどのバージョンのJavaScriptにコンパイルするかを選べます。TypeScriptが対応しているもっとも古いJavaScriptのバージョンはES3で、これはモダンブラウザ以前の古いブラウザにも対応できます。次に古いES5へのコンパイルでは、Internet Explore 9などの2012 年当時のモダンブラウザにも対忾できます。

TypeScript 的魅力不仅在于可以编译成旧版本的 JavaScript。ECMAScript 作为 JavaScript 的规范，每年都会进行一次主要版本更新，每次更新都会引入方便的新功能。TypeScript 遵循 ECMAScript 的规范，可以迅速采纳 ECMAScript 中采纳的新功能。

此外，TypeScript 已经提前引入了即将出现在下一个 ECMAScript 版本中的语言规范，换句话说，它几乎可以确定将在未来的 JavaScript 中使用的语言规范。

除了追随 ECMAScript，通过提前引入 ESNext，程序员可以在使用最新的 JavaScript 语法的同时，也能兼容旧环境的代码。

需要注意的是，使用新 API。例如，使用 ECMAScript 2015（ES6）引入的`Map`类和`Set`类编写的代码在 TypeScript 中编译，然后编译为 ES5，不会出现语法错误，但使用`Map`类和`Set`类的部分将导致运行时错误。这是因为 TypeScript 只负责将新语法转换为旧 JS 代码。如果需要在旧环境中使用新 API，则可以通过使用[core-js](https://github.com/zloirock/core-js)等 polyfill 来解决。

## TypeScript 是最受欢迎和最受喜爱的 AltJS 之一​

通常将用于编译成 JavaScript 使用的语言总称为“AltJS”。TypeScript 是 AltJS 的一种，除了 TypeScript 外，AltJS 还有许多其他语言。在这些语言中，TypeScript 是最受欢迎的。

Stack Overflow 针对约 65,000 名开发人员进行的调查发布了[最受欢迎的编程语言排名](https://insights.stackoverflow.com/survey/2020#most-popular-technologies)。这个排名不仅包括 AltJS，还包括 JavaScript、Java、C#等所有编程语言。在这个排名中，TypeScript 超过了 C 语言和 Ruby，排名第 9。

还有另一项调查，针对全球约 2 万名 JavaScript 用户进行的调查“[JavaScript 2020 的现状](https://2020.stateofjs.com/)”。根据这项调查，从 2017 年到 2020 年的 4 年间，TypeScript 连续四年获得了最高满意度。此外，93%的用户表示“满意，并且想再次使用”。

选择使用用户众多且满意度高的编程语言有许多优点。首先，信息丰富度很高。学习新语言或解决问题时，信息量对开发的便利性有着重要影响。

其次，TypeScript 拥有丰富的生态系统。有许多支持 TypeScript 的 IDE，如 VSCode 和 JetBrains IntelliJ IDEA，许多框架和包也支持 TypeScript。即使语言本身的规范再好，如果周围的开发环境不完善，就必须自己重新发明其他语言已经存在的工具和包。由于 TypeScript 的生态系统非常完善，因此不必担心这些问题。

最后，在招聘和就业方面，TypeScript 也具有优势。使用人数多意味着公司更容易找到程序员，对求职者来说也更容易找到项目。正如之前的调查结果所显示的那样，TypeScript 具有很高的满意度，采用这种语言的项目更容易受到程序员的欢迎，吸引到高度积极性的程序员。
