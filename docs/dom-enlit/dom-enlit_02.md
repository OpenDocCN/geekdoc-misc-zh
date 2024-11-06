# 介绍

这本书不是关于 DOM 编写或 [JavaScript](http://javascriptenlightenment.com/) 的详尽参考。然而，这可能是关于 DOM 编写的最详尽的一本书，而没有使用库/框架。围绕这个主题缺乏作者的原因并不是没有道理的。大多数技术作者不愿意涉足这个主题，因为传统浏览器之间存在的差异以及它们对 DOM 规范的实现（或缺乏实现）。

为了这本书的目的（即理解概念），我将绕过浏览器 API 的混乱和不断消失的浏览器差异，以揭示现代 DOM。没错，我将绕过丑陋的部分，专注于当下。毕竟，我们有像 jQuery 这样的解决方案来处理所有那些浏览器的丑陋，当处理已弃用的浏览器时，你应该绝对利用类似 jQuery 的东西。

虽然我并不提倡在 DOM 编写时只使用原生方法，但我写这本书的部分原因是让开发人员意识到在编写 DOM 时并不总是需要 DOM 库。我也写给那些有幸只需为单一环境编写 JavaScript 代码的人（例如一个浏览器、移动浏览器，或通过 PhoneGap 等方式将 HTML+CSS+JavaScript 转换为原生应用）。在理想情况下，你在这本书中学到的知识可能会使 DOM 库在某些情况下变得不再必要，比如仅在 Webkit 移动浏览器上部署一些轻量级的 DOM 编写。

## 谁应该阅读这本书

在我撰写这本书时，我特别考虑了两类开发人员。我假设这两类人已经具有中级到高级的 JavaScript、HTML 和 CSS 知识。第一类开发人员是那些对 JavaScript 或 jQuery 有一定了解，但从未花时间去理解 jQuery 这样的库的目的和价值（如果你愿意的话，可以理解为它的韵律）。通过这本书的知识，这类开发人员应该完全能够理解 jQuery 为 DOM 编写脚本提供的价值。不仅仅是价值，还有 jQuery 是如何抽象 DOM，以及 jQuery 在哪里以及为什么填补了空白。第二类开发人员是被委托编写仅在现代浏览器中运行或将被移植到多个操作系统和设备分发（例如 PhoneGap）的 HTML 文档的工程师，需要避免库的开销（即大小或大小与使用之间的关系）。

## 技术意图、允许性和限制

+   本书中包含的内容和代码是针对现代（IE9+，Firefox 最新版，Chrome 最新版，Safari 最新版，Opera 最新版）浏览器编写的。我的目标是只包含现代浏览器原生支持的概念和代码。如果我超出了这个目标，我会提醒读者。我通常避免在这本书中包含任何特定于某个浏览器或在现代浏览器中少数实现的内容。

+   我在这本书中并不试图教条地专注于特定的 DOM、CSS 或 HTML 规范。我的目标不是教条地代表特定的规范。考虑到工作中的规范数量以及浏览器正确实现规范的历史/状态，这将是一个过于庞大的任务（在我看来价值不大）。我已经在非常主观的方式上平衡了来自多个规范的内容（[文档对象模型（DOM）3 级核心规范](http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html)、[DOM4](http://www.w3.org/TR/dom/)、[文档对象模型 HTML](http://www.w3.org/TR/2003/REC-DOM-Level-2-HTML-20030109/html.html)、[元素遍历规范](http://www.w3.org/TR/ElementTraversal/)、[选择器 API 2 级](http://www.w3.org/TR/selectors-api2/)、[DOM 解析和序列化](http://html5.org/specs/dom-parsing.html)、[HTML 5 参考](http://dev.w3.org/html5/html-author/)、[HTML 5 - 用于 HTML 和 XHTML 的词汇表和相关 API](http://www.w3.org/TR/html5/)、[HTML Living Standard](http://www.whatwg.org/specs/web-apps/current-work/multipage/)、[HTML 5 - 面向 Web 开发者的技术规范](http://developers.whatwg.org/)、[DOM Living Standard](http://dom.spec.whatwg.org/)）。这本书的内容更多地基于社区的发展方向，而不是教条地试图表达特定的规范。

+   我涵盖了一些精心挑选的与 DOM 无关的主题。我在这本书中包含这些主题是为了帮助读者建立对 DOM 与 CSS 和 JavaScript 的关系有正确的理解。

+   我故意省略了与 XML 或 XHTML 相关的任何细节。

+   我故意省略了表单和表格 API，以保持书籍的简洁。但我可以看到这些部分在未来可能会被添加进来。

## 许可证

《DOM Enlightenment》HTML 版本采用[知识共享署名-非商业性使用-禁止演绎 3.0](http://creativecommons.org/licenses/by-nc-nd/3.0/)无端许可证发布。

## 实体书和电子书

[奥莱利](http://oreilly.com/)将在不久的将来发布并销售实体书和电子书。
