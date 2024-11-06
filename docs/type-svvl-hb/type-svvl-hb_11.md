# ECMAScript

> 原文：[`typescriptbook.jp/overview/ecmascript`](https://typescriptbook.jp/overview/ecmascript)

ECMAScript 是 JavaScript 的规范。TypeScript 也符合 ECMAScript 的规范。本文将解释 ECMAScript 是什么，规范修订的过程，以及 ECMAScript 与浏览器之间的关系。

## JavaScript 和 ECMAScript 的关系​

ECMAScript 是定义 JavaScript 规范的内容。规范是一系列规则，当浏览器等加载 JavaScript 时，决定应该如何解释语法，以及处理应该如何进行的内容。尽管 ECMAScript 有一个不同的名称，但并不存在与 JavaScript 不同的语言。

从历史上看，为了标准化 JavaScript，ECMAScript 被制定出来。JavaScript 是由 Netscape 公司开发的语言。Netscape 公司发布后不久，Microsoft 公司也以 JScript 的名义实现了它。为了标准化 JavaScript，Netscape 公司请求国际标准化组织 Ecma 国际进行标准化。由 Ecma 标准化的 JavaScript 被称为“ECMAScript”。

当前的 ECMAScript 是 JavaScript 的规范。浏览器等 JavaScript 实现需要遵循的规范。由于这种关系，有时会用 JavaScript 来指代 ECMAScript 的实现。ECMAScript 是一种规范，因此并不存在名为 ECMAScript 的程序。这意味着它不是可下载或安装的东西。

有关 JavaScript 规范被命名为“ECMAScript”的原因有多种说法。其中一种说法是，当时竞争对手的 Netscape 公司和 Microsoft 公司达成的妥协方案是 ECMAScript。Netscape 公司以 JavaScript 的名义开发，而 Microsoft 公司以 JScript 的名义开发。商标问题也是其中一个原因。当时 JavaScript 是 Sun 拥有的商标。后来，这些权利被 Oracle 接管。

ECMAScript 由 Ecma 国际制定。该组织制定了各种信息通信技术的国际标准。每个标准都有一个编号。ECMAScript 的规范编号是 ECMA-262。还有其他一些，如 JSON（ECMA-404）和 C#（ECMA-334）。Ecma 国际有各种专门委员会，负责制定 ECMAScript 的委员会称为 TC39。

## ECMAScript 的规范修订​

每年都会对 ECMAScript 进行一次规范修订。每次修订都会提升版本号。ECMAScript 的版本号是根据发布的公元年份命名的。例如，2021 年修订的 ECMAScript 将被称为 ES2021。TypeScript 也会随着 ECMAScript 的规范修订而更新。

ECMAScript 的修订始于征集提案。提交的修订提案可以在[TC39 的 GitHub](https://github.com/tc39/proposals)上找到。

随着进展，每个提案都会被分配从阶段 0 到阶段 4 的等级。满足条件后，可以进入相应的阶段。

| **阶段** | **条件** |
| --- | --- |
| 0 稻草人 | 无 |
| 1 提案 | 需要有决定提案的冠军（委员会的修订推动伙伴）。需要有解释问题和解决方案的存储库。最好有演示 |
| 2 草案 | ECMAScript 的规范描述语言中包含主要部分的规范 |
| 3 候选 | 需要有完整的规范书。需要有审阅者和 ECMAScript 编辑者的签名 |
| 4 完成 | 至少有两个 JS 引擎实现。已向 ECMAScript 编辑者发送了拉取请求，并获得批准 |

阶段 2 及以下的提案可能会导致规范发生重大变化。提案也有可能被撤回。

达到第 3 阶段时，修订变得更加确定。TypeScript 将支持达到第 3 阶段的提案。在这个阶段，浏览器也会实现第 3 阶段的提案。有时会有实现延迟的情况。

到达第 4 阶段时，几乎肯定会成为 ECMAScript 的规范。第 4 阶段的提案通常会在每年 6 月的 ECMAScript 修订中被纳入。修订的大致年度时间表如下。

+   2 月：创建候选草案

+   3 月：将阶段 4 的提案纳入，并批准最终规范

+   4 月至 6 月：ECMA CC 和 ECMA GA 的审查期间

+   6 月：经 ECMA 全体会议批准，确定修订规范

## ECMAScript 和浏览器的规范​

ECMAScript 确定的客户端 JavaScript 规范是部分的。ECMAScript 确定的范围包括语言语法、语法解释方式、核心 API 等语言的核心部分。例如，它规定了以下内容。

+   函数声明的语法如下

+   当声明变量时，JavaScript 引擎会执行以下操作

+   `String`和`Array`对象具有以下方法

与浏览器相关的 JavaScript 部分由 HTML Living Standard 确定。在浏览器中使用 JavaScript 时，会涉及`window`对象、`HTMLDivElement`、本地存储等 API。这些由[HTML Living Standard](https://html.spec.whatwg.org/)规定。该标准由与 Ecma 国际不同的标准化组织 WHATWG 制定。

即使在 JavaScript 的功能中，也有分配给 ECMAScript 和 HTML Living Standard 的角色。例如，模块。ECMAScript 规定了模块的规范。 `import`和`export`语法以及模块内部的规范由 ECMAScript 规定。另一方面，HTML Living Standard 规定了模块的具体加载方法。例如，`import "specifier";`中的 specifier 部分应该写什么字符串，以及模块应该以何种顺序加载等，都由 HTML Living Standard 规定。

## 📄️ 🚧模块

实验性！本页面是正在撰写的草稿。结构可能会发生重大变化，请注意链接可能会失效。本页内容是根据 import、export 和 require 重新构建和补充的。

“JavaScript”一词涵盖了多个规范。

## ECMAScript 与浏览器的关系​

在拆分主要浏览器的内部结构时，有称为渲染引擎或 JavaScript 引擎的组件单元。

JavaScript 引擎是实现 ECMAScript 的模块。JavaScript 引擎主要有 V8、SpiderMonkey 和 JavaScriptCore。

渲染引擎是集成了 JavaScript 引擎的浏览器显示功能的模块。著名的渲染引擎有 Blink、Gecko 和 WebKit。例如，Blink 采用了 V8 作为 JavaScript 引擎。渲染引擎不仅解释 JavaScript，还解释 HTML 和 CSS，并综合进行屏幕绘制。

浏览器集成了渲染引擎，并附带其他功能，如书签功能，以应用程序形式提供给用户。例如，Google Chrome 集成了 Blink，Safari 集成了 WebKit。浏览器也可能更改渲染引擎。Microsoft Edge 曾经采用 EdgeHTML，但后来转而使用了与 Google Chrome 相同的 Blink。Opera 的渲染引擎曾经是 Presto，但后来改为了 Blink。

即使是同一品牌的浏览器，iOS 版本的浏览器渲染引擎也是 WebKit。例如，Google Chrome 采用了 Blink，但 iOS 版的 Google Chrome 的渲染引擎是 WebKit。这是因为 iOS 的渲染引擎只允许使用 WebKit。

浏览器、渲染引擎、JavaScript 引擎、ECMAScript 的关系图

![](img/browser-rendering-engine-javascript-engine-ecmascript-relations.svg)

TypeScript 程序员理解浏览器和引擎的对应关系至关重要。了解引擎就等于了解程序开发的执行环境。引擎尽量遵循规范，但不同引擎的实现可能有所不同。某些引擎可能没有实现某些规范。此外，某些浏览器可能使用旧版引擎。

编写测试时，如果了解了浏览器和引擎的组合，那么采用相同引擎的浏览器可能可以省略测试。就像 iOS 的 WebKit 一样，即使是同一品牌的浏览器，引擎也可能不同。在这种情况下，可以做出增加覆盖范围的浏览器测试的决定。

##### 分享学习

・ECMAScript（ES）是 JavaScript 的规范

・ES 由 Ecma International 的 TC39 委员会制定

・ES 每年 6 月进行修订

・ES 的修订提案是公开招标，并在第 4 阶段被采纳

・浏览器具有渲染引擎和 JS 引擎

・JS 引擎实现 ES

『生存 TypeScript』

[分享此内容到 Twitter](https://twitter.com/intent/tweet?text=%E3%83%BBECMAScript(ES)%E3%81%AFJavaScript%E3%81%AE%E4%BB%95%E6%A7%98%0A%E3%83%BBES%E3%81%AFEcma%E3%82%A4%E3%83%B3%E3%82%BF%E3%83%BC%E3%83%8A%E3%82%B7%E3%83%A7%E3%83%8A%E3%83%AB%E3%81%AETC39%E5%A7%94%E5%93%A1%E4%BC%9A%E3%81%8C%E5%AE%9A%E3%82%81%E3%82%8B%0A%E3%83%BBES%E3%81%AF%E6%AF%8E%E5%B9%B46%E6%9C%88%E3%81%AB%E6%94%B9%E5%AE%9A%E3%81%95%E3%82%8C%E3%82%8B%0A%E3%83%BBES%E3%81%AE%E6%94%B9%E5%AE%9A%E6%8F%90%E6%A1%88%E3%81%AF%E5%85%AC%E5%8B%9F%E3%81%95%E3%82%8C%E3%80%81%E3%82%B9%E3%83%86%E3%83%BC%E3%82%B84%E3%81%A7%E6%8E%A1%E7%94%A8%E3%81%95%E3%82%8C%E3%82%8B%0A%E3%83%BB%E3%83%96%E3%83%A9%E3%82%A6%E3%82%B6%E3%81%AF%E3%83%AC%E3%83%B3%E3%83%80%E3%83%AA%E3%83%B3%E3%82%B0%E3%82%A8%E3%83%B3%E3%82%B8%E3%83%B3%E3%81%A8JS%E3%82%A8%E3%83%B3%E3%82%B8%E3%83%B3%E3%82%92%E6%8C%81%E3%81%A4%0A%E3%83%BBJS%E3%82%A8%E3%83%B3%E3%82%B8%E3%83%B3%E3%81%AFES%E3%82%92%E5%AE%9F%E8%A3%85%E3%81%99%E3%82%8B%0A%0A%E3%80%8E%E3%82%B5%E3%83%90%E3%82%A4%E3%83%90%E3%83%ABTypeScript%E3%80%8F%E3%82%88%E3%82%8A)
