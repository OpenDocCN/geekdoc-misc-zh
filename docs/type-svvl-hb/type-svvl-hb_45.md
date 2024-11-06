# TypeScript 学习资源

> 原文：[`typescriptbook.jp/learning-resources`](https://typescriptbook.jp/learning-resources)

TypeScript 拥有许多资源可供学习和调查，包括本书和 Microsoft 提供的资源。

本页将介绍本书解说后，或者在阅读过程中也可以使用的关于 TypeScript 的信息源。此外，本页的后半部分将解释学习和开发中非常重要的官方文档的结构和阅读方法等攻略方法。

高效利用资源

在完全阅读本页介绍的所有资源是困难且低效的，因此建议根据各信息源的角色和水平进行取舍，部分阅读，或根据目的选择使用。

## 资源介绍​

### Microsoft 官方信息源​

Microsoft 提供的主要信息源介绍。

| 资源 | 特点 |
| --- | --- |
| [TypeScript 文档](https://www.typescriptlang.org/docs/) | 这是 TypeScript 的官方文档。这是最重要的信息源，是学习和开发时必不可少的参考。本页的后半部分将详细解释内容和攻略方法。 |
| [Microsoft 开发者博客](https://devblogs.microsoft.com/typescript/) | 这是 Microsoft 开发者博客中关于 TypeScript 的文章。您可以了解到关于新版本的信息以及 TypeScript 的最新动态。 |
| [常见问题解答](https://github.com/microsoft/TypeScript/wiki/FAQ) | 这是在开发存储库的 wiki 上整理的关于 TypeScript 的常见问题集。提供了关于行为和实践等方面的 Why/What/How/Should 类型的问题和答案。 |

尽管官方提供的信息源中最重要的是官方文档，但是一些未在官方文档中提及的细微行为和概念等内容需要参考开发存储库中的一些信息源。

| 资源 | 特点 |
| --- | --- |
| [路线图](https://github.com/microsoft/TypeScript/wiki/Roadmap) | 这是 TypeScript 将来要添加的功能的路线图。在过去的各个版本中引入的功能的拉取请求都列在这里，每个拉取请求都包含了语言开发者对概念和功能的详细说明。 |
| [docs/spec-ARCHIVED.md](https://github.com/microsoft/TypeScript/blob/3c99d50da5a579d9fa92d02664b1b66d4ff55944/doc/spec-ARCHIVED.md) | 这是 TypeScript 的旧规范书，记录了一些官方文档中未提及的细微行为和概念。由于已从主分支中删除，请注意。 |
| [compiler/checker.ts](https://raw.githubusercontent.com/microsoft/TypeScript/main/src/compiler/checker.ts) | 这是类型检查器的实现源代码文件。当前的 TypeScript 没有更新的规范书，这是唯一记录类型检查行为的注释文档。 |

### 第三方信息源​

作为受欢迎的第三方信息源，介绍一些学习资源。

| 资源 | 特点 |
| --- | --- |
| [roadmap.sh](https://roadmap.sh/typescript) | 这是以路线图形式总结的开发者应学习内容的网站“roadmap.sh”的 TypeScript 版本。在这个网站上，您可以以路线图的形式概览 TypeScript 语言的整体情况和学习路径。 |
| [TypeScript 深入浅出 日本語版](https://typescript-jp.gitbook.io/deep-dive/) | 这是一本在线开放源的解说书，虽然内容紧凑，但你可以深入了解 TypeScript 的高级内容。原版是英文的，但由志愿者翻译成了日文，因此可以用日文阅读。 |
| [Programming TypeScript ―构建可扩展的 JavaScript 应用程序](https://www.oreilly.co.jp/books/9784873119045/) | 这是由 O'Reilly Japan 出版的 TypeScript 入门书。除了 TypeScript 语法之外，还解释了类型安全性，类型检查器是什么，以及类型的根本概念，让您从头开始理解 TypeScript 的类型系统。 |
| [面向专业人士的 TypeScript 入门 从编写安全代码到高级类型使用](https://gihyo.jp/book/2022/978-4-297-12747-3) | 这是由技术评论社出版的 TypeScript 入门书。通常被称为“蓝莓书”，涵盖了 TypeScript 以及 JavaScript 的解释。 |
| [播放列表:最易懂的 TypeScript 入门](https://www.youtube.com/watch?v=kd8VH10jXwc&list=PLX8Rsrpnn3IW0REXnTWQp79mxCvHkIrad) | 这是由とらゼミ提供的 TypeScript 解说视频系列。您可以通过视频轻松了解 TypeScript 的基础知识。 |

#### JavaScript 学习资源​

学习 TypeScript 必须学习 JavaScript。在这里，我们将介绍一些著名的 JavaScript 学习资源。实际上，在学习 TypeScript 的过程中，经常会遇到需要更深入了解 JavaScript 的情况，因此建议在需要时参考这些文档。

| 资源 | 特点 |
| --- | --- |
| [MDN Web Docs](https://developer.mozilla.org/ja/docs/Web/JavaScript) | 记载了 JavaScript 语法和功能的 Web 文档，由 Mozilla 运营并以开源形式撰写。涵盖了 HTML、CSS、WebAPI 等与 Web 相关技术，可在各种场景中作为参考使用。 |
| [JavaScript Primer 迷わないための入門書](https://jsprimer.net) | 基于 ES2015 及更高版本功能的 JavaScript 学习 Web 文档。为了便于阅读，还出版了书籍版本，如果想要阅读书籍版本，可以从 Amazon 或达人出版会处获取。 |

与本书一样，它们的内容都是在 GitHub 上管理的，因此可以通过创建拉取请求或问题来做出贡献，这是它们的显著特点。

## 官方文档的攻略​

由于 TypeScript 官方文档是用英语编写的，而且内容很多，可能会让人望而却步。

然而，在学习和开发 TypeScript 时，为了了解各功能的准确信息和详细信息，阅读官方文档是必不可少的，因此，在本节中，我们将重点介绍核心手册以及官方文档的结构和阅读方法。

由于官方文档经常会在阅读本书后继续发挥作用，因此请务必掌握阅读方法，与官方文档建立良好关系。

### 构成要素​

首先，让我们从官方文档的构成要素开始了解。TypeScript 官方文档由以下列出的多个部分组成。

| 部分 | 内容 |
| --- | --- |
| **开始** | 根据学习者的背景和技能制定的介绍部分。 |
| **手册** | 手册是语言功能和行为的全面指南。涵盖了 TypeScript 在日常使用中的功能和行为，可以在几小时内阅读完毕。 |
| **参考** | 手册未涵盖的高级话题的参考部分。包括实用类型、命名空间、类型兼容性等话题。 |
| 教程 | 在几种典型环境中进行 TypeScript 的引入和使用的教程。 |
| 声明文件 | 声明文件(`.d.ts`)的解释文档。在包分发等情况下创建声明文件时，这一部分会很有用。 |
| JavaScript | 记载了在使用 JavaScript 项目中获得 TypeScript 工具等好处所需的信息等。 |
| 项目配置 | 有关项目配置的文档。解释了如何设置 tsconfig，如果想了解编译器选项的详细信息，可以查看这一部分。 |
| **速查表** | 将语法等内容以图像形式简明地总结的速查表。在想要俯瞰 TypeScript 语法时很有用。 |
| 新功能 | 每个版本新增功能的介绍页面。在新版本页面上，实际添加功能的拉取请求会链接到该页面，因此，如果想了解更详细的行为说明，可以通过跟随该链接阅读开发者的解释。 |

通常情况下，提到官方文档时通常指的是手册，但在 TypeScript 官方网站上有一个名为“[TypeScript Documentation](https://www.typescriptlang.org/docs/)”的页面，其中包含了一系列文档，包括速查表等，这些文档被视为官方文档。

然而，并不需要一口气阅读所有部分。初学者应重点阅读的部分和高效阅读的方法有很多。

### 基本攻略方针​

官方文档的攻略方法是“根据学习水平和情况调整官方文档的阅读方式”，这种方法可以有效地阅读大量的官方文档。

具体而言，以下方法是顺畅且推荐的：

+   (A) 了解官方文档的结构和特点

+   (B) 阅读「开始」部分的介绍

+   (C) 从头开始阅读手册

+   (D) 当需要详细知识时阅读参考资料等

+   (E) 阅读 TypeScript 开发存储库中的一手信息

+   (X) 通过速览“速查表”了解语法概述

基本上，按照(A)到(E)的顺序进行，可以逐渐扩展知识。

通过阅读(A)部分的内容即可完成，但特别是当将官方文档视为学习资源时，“开始”和手册变得重要，成为初学者应重点阅读的部分。花时间重点阅读这两部分，而参考资料等则可以在需要时或有空闲时间时随时查阅，这样可以高效地掌握阅读内容。

此外，有些功能在官方文档中可能解释不足。如果想了解更详细的行为等内容，可以通过阅读实现了该功能的拉取请求的说明来了解细节。您可以从 TypeScript 的代码库中了解每个功能是在哪个版本中引入的，可以通过“新功能”页面或开发存储库的“[路线图](https://github.com/microsoft/TypeScript/wiki/Roadmap)”来了解这些信息，然后从这些资料中访问拉取请求以获取详细信息。

(X)的速查表详细总结了 TypeScript 的语法，通过查看它，您可以概览所需的知识，因此在需要时可以查看。

公式文档的攻略方法基本方针如上所述，接下来将解释核心的手册内容。

### 手册版本​

TypeScript 自 2012 年首次发布以来已经有 10 多年的历史。在这段时间里，语言不断更新，不断演进，官方文档也随之发展。

## 📄️ 背景下的 TypeScript 诞生

TypeScript 是一种旨在使 JavaScript 开发大型应用程序更容易的编程语言。

官方文档包含许多部分，但其中“手册”部分尤为重要。手册是 TypeScript 语言的全面指南，为学习者提供关于日常使用的 TypeScript 功能和行为的深入理解。

此外，作为官方文档的显着进化，2021 年发布了被称为“v2”的新手册版本。v2 之前的手册被称为“v1”，现在可以从[存档存储库](https://github.com/microsoft/TypeScript-Handbook)中查看，因为它已被弃用。

注意

v2 手册的发布相对较新，因此请注意，迄今为止的许多流行入门书籍和在线资源都反映了 v1 的内容。

### 手册的特点​

v2 手册是在开发者博客文章“[宣布新的 TypeScript 手册](https://devblogs.microsoft.com/typescript/announcing-the-new-typescript-handbook/)”中提到的一些限制下编写的。

+   将 JavaScript 教学交给专家 (Leave teaching JavaScript to the experts)

+   逐步教授 (Teach incrementally)

+   让编译器说话 (Let the compiler do the talking)

+   撰写日常案例 (Write for the everyday cases)

突出的是，手册并未从头开始解释 JavaScript 的知识，而是通过委托其他书籍和网络资源来使内容更加简洁。手册的目的之一是让工程师能够理解作为语言超集的 TypeScript 是如何构建在 JavaScript 之上的，因此，手册假定读者具有一定程度的 JavaScript 知识和背景。

然而，为了满足具有不同技能水平的读者，手册在外部提供了一个“入门”部分，供初学者阅读，包括其他语言学习者在内，建议初学者从这部分开始阅读。

#### 与 Survival TypeScript 一起使用​

如上所述，手册并未解释 JavaScript 原本具有的功能或语法等。然而，由于理解 TypeScript 需要理解 JavaScript 的事实，因此如果您希望同时学习 JavaScript，本书的内容将非常有用。

## 📄️ JavaScript is part of TypeScript

TypeScript 的语法是对 JavaScript 语法的扩展。TypeScript 扩展的语法主要涉及类型部分。除此之外，大部分语法都源自 JavaScript。因此，原生 JavaScript 也可以被视为 TypeScript。例如，下面的代码是 100%JavaScript，但 TypeScript 编译器可以解析它并进行静态检查。

如果在阅读本书时发现了感兴趣的功能或想要深入了解的内容，可以在整个官方文档中搜索，包括手册。如果您不擅长英语，建议您在仔细阅读本书内容并理解后，再阅读相关官方文档页面。本书包含了许多原始英文单词，您可以使用这些单词在官方文档中进行搜索，以便轻松找到想要阅读的部分。

[## 📄️ Index: Symbols and Keywords

JavaScript 和 TypeScript 的代码中会使用?.之类的符号和 as 之类的关键字。这些符号和关键字很难通过 Google 搜索来查找其含义。

此外，与本书类似的是，手册并未涵盖所有边缘案例或过于特殊的功能，而是专注于日常案例。超出这一范围的内容将在参考部分的页面中提供。

与官方文档相比，本书更加注重实践性。第三章“用于学习 TypeScript 的实践”涵盖了实现各种应用程序的方法，第五章“技巧”介绍了编码技巧，此外，本书还介绍了一些实践中有用的实践。因此，通过根据需求和情况灵活使用官方文档和本书，可以更有效地学习。

请意识到语言的层次

在学习 TypeScript 时，建议同时使用本书和官方文档，但如果您想更深入地了解 JavaScript 的功能和语法，请同时使用 MDN Web 文档，并参考 ECMAScript 规范。

+   TypeScript → [官方文档](https://www.typescriptlang.org/docs/)

+   JavaScript → [MDN Web 文档](https://developer.mozilla.org/ja/docs/Web/JavaScript)

+   ECMAScript → [ecma262](https://tc39.es/ecma262/)

TypeScript 是一种将“类型系统+运行时+语言规范”等多个语言、规范、API 等层次分开存在的语言，因此在进行行为和问题调查等工作时，需要分别查阅每个层次的文档。当您想了解 TypeScript 的功能、设置，即关于类型的功能（类型注解、类型推断、类型运算符等）或编译器选项时，请参考 TypeScript 的官方文档。

请意识到您想要了解哪方面的信息，如果您想了解 JavaScript 的语法或 ECMAScript 规范，请阅读相关文档。

### 让我们阅读介绍​

在开始阅读本书之前，建议先阅读“Get Started”部分的介绍。在这个部分的页面中，提供了 5 个文档，以便不同技能水平和背景的读者能够轻松了解 TypeScript 的特点。

| 页面 | 内容 |
| --- | --- |
| [面向新手程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-from-scratch.html) | 针对选择 TypeScript 作为第一门语言的新手程序员的介绍。 |
| [面向 JavaScript 程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes.html) | 针对具有 JavaScript 经验的程序员的介绍。 |
| [面向 Java/C# 程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes-oop.html) | 为具有 Java 或 C# 等面向对象编程（OOP）经验的程序员提供的入门介绍。 |
| [面向函数式程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes-func.html) | 针对具有 Haskell 或 ML 等函数式编程（FP）经验的程序员的介绍。 |
| [5 分钟了解 TypeScript 工具](https://www.typescriptlang.org/docs/handbook/typescript-tooling-in-5-minutes.html) | 介绍了从 TypeScript 安装到构建简单 Web 应用程序的方法。适合立即使用 TypeScript 的读者。 |

请根据自己的技能和背景选择适合的介绍页面。下面介绍了每个技能水平的人应该阅读的页面内容，但请注意，“Get”

每个“Started”页面都包含了**仅在该页面上才有的重要知识和思维方式**，因此，建议您在有时间的情况下也阅读其他页面。

#### 🧑‍💻 新手程序员​

如果 TypeScript 是您第一门编程语言，请从“[面向新手程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-from-scratch.html)”页面开始阅读，这样您就可以获得今后学习的指导方向。

文档内容涵盖了 JavaScript 的历史，以及 JavaScript 和 TypeScript 的关系等简要说明。

由于本书的写作约束为“JavaScript 的解释交给专家”，因此基本上没有关于 JavaScript 功能或语法的解释。因此，在介绍 JavaScript 学习资源之后，本页面以“学习 TypeScript 需要先学习 JavaScript”为结尾，鼓励学习 JavaScript。

#### 🧙 掌握了 JavaScript 经验的学习者​

如果您具有 JavaScript 方面的知识或经验，则建议从“[面向 JavaScript 程序员的 TypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes.html)”页面开始阅读。这个页面非常有用，可以快速了解 TypeScript 的核心功能和概念。

+   类型推断

+   类型定义

+   型の合成(ユニオン型とジェネリクス)

+   構造的型システム

このページを読めばTypeScriptでの重要な概念については把握することができるため、ハンドブックではそれらの知識をさらに拡張していけばよいことになります。

#### 👨‍🚀 オブジェクト指向プログラミングの経験がある学習者​

JavaやC#などのオブジェクト指向プログラミング(OOP)の経験がある学習者は「[Java/C#プログラマーのためのTypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes-oop.html)」のページを読むことでTypeScriptにおいて、クラスやオブジェクト指向の考え方の違いについて学ぶことができます。

公称型(nominal typing)を採用しているJavaやC#に対して、TypeScriptは構造的部分型(structural subtyping)を採用してることから知っておくべき違いや型の考え方についての重要なアイデアが提示されています。

## 📄️ 構造的型付け

プログラミング言語にとって、型システムは大事なトピックです。型システムとは、プログラム内のさまざまな値や変数に「型」を割り当てる決まりを指します。この決まりによってデータの性質や扱い方が決まります。特に、どのように型と型を区別するのか、逆に、どのように型同士が互換性ありと判断するかは、言語の使いやすさや安全性に直結するテーマです。

#### 🦸‍♂️ 関数型プログラミングの経験がある学習者​

HaskellやMLなどの関数型プログラミング(FP)の経験がある学習者は「[関数型プログラマーのためのTypeScript](https://www.typescriptlang.org/docs/handbook/typescript-in-5-minutes-func.html)」のページを読むことで、それらの関数型言語との類似機能や違いなどを学びながらTypeScriptについて知ることができます。

内容としてはHaskellの型システムとの相違点と類似点についての解説となっています。具体的には単位型(unit type)や、ポイントフリースタイルプログラミング(point-free programming)、高カインド型(higher-kinded types)などをTypeScriptでのどのように扱うかなどの解説があります。

### ハンドブックの読み進め方​

ハンドブックは次のようなセクション構成となっています。

| ページ | 内容 |
| --- | --- |
| [TypeScriptハンドブック](https://www.typescriptlang.org/docs/handbook/intro.html) | ハンドブックの構成と目的についての説明 |
| [基本的な考え方](https://www.typescriptlang.org/docs/handbook/2/basic-types.html) | TypeScriptにおける基本的な考え方などについての説明 |
| [日常的な型](https://www.typescriptlang.org/docs/handbook/2/everyday-types.html) | 日常的に使用するあらゆる型についての説明 |
| [型の絞り込み](https://www.typescriptlang.org/docs/handbook/2/narrowing.html) | 型の絞り込みについての説明 |
| [関数についてさらに](https://www.typescriptlang.org/docs/handbook/2/functions.html) | 関数の型についての詳細説明 |
| [オブジェクトの型](https://www.typescriptlang.org/docs/handbook/2/objects.html) | オブジェクトの型についての詳細説明 |
| Type Manipulation | 型から新しい型を作成するための方法について解説したページを収めたセクションです。 |
| [クラス](https://www.typescriptlang.org/docs/handbook/2/classes.html) | アクセス修飾子やクラスの型注釈の方法などの説明 |
| [モジュール](https://www.typescriptlang.org/docs/handbook/2/modules.html) | モジュール解決などについての説明 |

「Type Manipulation」ではジェネリクスや型演算子などを利用して型から新しい型を作成するための方法について解説したページを収めたセクションです。このセクションは次のようなページ構成になっています。

| ページ | 内容 |
| --- | --- |
| [他の型から型を作成する方法](https://www.typescriptlang.org/docs/handbook/2/types-from-types.html) | 他の型から型を作成するための方法についてについての説明 |
| [ジェネリクス](https://www.typescriptlang.org/docs/handbook/2/generics.html) | 型をパラメータとして取るジェネリクスについての説明 |
| [Keyof 型演算子](https://www.typescriptlang.org/docs/handbook/2/keyof-types.html) | `keyof`型演算子を利用して新しい形を作る方法についての説明 |
| [typeof 型演算子](https://www.typescriptlang.org/docs/handbook/2/typeof-types.html) | `typeof`型演算子を利用して新しい型を作る方法についての説明 |
| [索引访问类型](https://www.typescriptlang.org/docs/handbook/2/indexed-access-types.html) | 描述了如何通过`Type['a']`语法访问类型的子集 |
| [条件类型](https://www.typescriptlang.org/docs/handbook/2/conditional-types.html) | 描述了在类型系统中作为语句行为的条件类型 |
| [映射类型](https://www.typescriptlang.org/docs/handbook/2/mapped-types.html) | 描述了通过映射现有类型的属性来创建类型的方法 |
| [模板文字类型](https://www.typescriptlang.org/docs/handbook/2/template-literal-types.html) | 描述了通过模板文字字符串修改属性的映射类型 |

出于“逐步教授”的写作限制，手册被设计成可以直线阅读，避免尽可能提及未解释的功能，而是逐步积累知识。因此，阅读的基本指导原则是**从头开始顺序阅读**。

如果您对 TypeScript 完全不了解，那么在阅读完“入门”部分的介绍页面后，只需阅读“[基础知识](https://www.typescriptlang.org/docs/handbook/2/basic-types.html)”和“[日常类型](https://www.typescriptlang.org/docs/handbook/2/everyday-types.html)”就可以了解 TypeScript 的概要。

由于每个知识都被模块化为页面，所以，可以跳过已知内容，仅阅读想要了解的页面，这种阅读方法也是有效的。不仅仅是手册的章节，特别是参考文献的部分适用于这种阅读方式。例如，有关引用页面的实用类型的介绍，关于基本类型操作符的知识在手册的“类型操作”部分有详细解释。

与其阅读官方文档，不如利用本书，因为它更细致地将知识模块化，这样一来，在阅读官方文档的同时，可以阅读到更易懂的日语解释。
