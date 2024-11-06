# 目录

##### 第一章 - 节点概述

###### 1.1 文档对象模型（也称为 DOM）是 JavaScript 节点对象的层次结构/树

###### 1.2 节点对象类型

###### 1.3 子节点对象继承自 *Node* 对象

###### 1.4 用于操作节点的属性和方法

###### 1.5 识别节点的类型和名称

###### 1.6 获取节点的值

###### 1.7 使用 JavaScript 方法创建元素和文本节点

###### 1.8 使用 JavaScript 字符串创建和添加元素和文本节点到 DOM 中

###### 1.9 将 DOM 树的部分提取为 JavaScript 字符串

###### 1.10 使用 *appendChild()* 和 *insertBefore()* 将节点对象添加到 DOM 中

###### 1.11 使用 *removeChild()* 和 *replaceChild()* 移除和替换节点

###### 1.12 使用 *cloneNode()* 克隆节点

###### 1.13 理解节点集合（即 *Nodelist* 和 *HTMLcollection*）

###### 1.14 获取所有直接子节点的列表/集合

###### 1.15 将 *NodeList* 或 *HTMLCollection* 转换为 JavaScript *Array*

###### 1.16 遍历 DOM 中的节点

###### 1.17 使用 *contains()* 和 *compareDocumentPosition()* 验证节点在 DOM 树中的位置

###### 1.18 如何确定两个节点是否相同

##### 第二章 - 文档节点

###### 2.1 *document* 节点概述

###### 2.2 *HTMLDocument* 属性和方法（包括继承的）

###### 2.3 获取一般 HTML 文档信息（标题、URL、引用者、lastModified、compatMode）

###### 2.4 *document* 子节点

###### 2.5 *document* 提供了 *<!DOCTYPE>*、*<html lang="en">*、*<head>* 和 *<body>* 的快捷方式

###### 2.6 使用 *document.implementation.hasFeature()* 检测 DOM 规范/特性

###### 2.7 获取 *document* 中焦点/活动节点的引用

###### 2.8 确定 *document* 或 *document* 中的任何节点是否具有焦点

###### 2.9 *document.defaultview* 是指向 head/global 对象的快捷方式

###### 2.9 使用 *ownerDocument* 从 *element* 获取对 *Document* 的引用

##### 第三章 - 元素节点

###### 3.1 *HTML*Element* 对象概述

###### 3.2 *HTML*Element* 对象属性和方法（包括继承的）

###### 3.3 创建元素

###### 3.4 获取元素的标签名称

###### 3.5 获取元素属性和值的列表/集合

###### 3.6 获取、设置和移除元素的属性值

###### 3.7 验证元素是否具有特定属性

###### 3.8 获取类属性值列表

###### 3.9 向类属性添加和移除子值

###### 3.10 切换类属性值

###### 3.11 确定类属性值是否包含特定值

###### 3.12 获取和设置 data-*属性

##### 第四章 - 元素节点选择

###### 4.1 选择特定元素节点

###### 4.2 选择/创建元素节点列表（也称为*NodeList*）

###### 4.3 选择所有直接子元素节点

###### 4.4 上下文元素选择

###### 4.5 预配置的元素节点选择列表

###### 4.6 使用*matchesSelector()*验证将选择元素

##### 第五章 - 元素节点几何和滚动几何

###### 5.1 元素节点大小，偏移和滚动概述

###### 5.2 获取元素相对于*offsetParent*的*offsetTop*和*offsetLeft*值

###### 5.3 使用*getBoundingClientRect()*获取元素相对于视口的顶部，右侧，底部和左侧边框偏移

###### 5.4 获取元素在视口中的大小（边框 + 填充 + 内容）

###### 5.5 获取元素在视口中的大小（填充 + 内容），不包括边框

###### 5.6 使用*elementFromPoint()*在特定点获取视口中最顶部的元素

###### 5.7 使用*scrollHeight*和*scrollWidth*获取正在滚动的元素的大小

###### 5.8 使用*scrollTop*和*scrollLeft*获取和设置从顶部和左侧滚动的像素

###### 5.9 使用*scrollIntoView()*将元素滚动到视图中

##### 第六章 - 元素节点内联样式

###### 6.1 样式属性（也称为元素内联 CSS 属性）概述

###### 6.2 获取，设置和移除单个内联 CSS 属性

###### 6.3 获取，设置和移除所有内联 CSS 属性

###### 6.4 使用*getComputedStyle()*获取元素的计算样式（即包括来自级联的任何实际样式）

###### 6.5 使用*class*和*id*属性在元素上应用和移除 css 属性

##### 第七章 - 文本节点

###### 7.1 *文本*对象概述

###### 7.2 *文本*对象和属性

###### 7.3 空格创建*文本*节点

###### 7.4 创建和注入*文本*节点

###### 7.5 使用*.data*或*nodeValue*获取*文本*节点值

###### 7.6 使用 *appendData()*、*deleteData()*、*insertData()*、*replaceData()*、*subStringData()* 操作 *Text* 节点

###### 7.7 当存在多个兄弟 *Text* 节点时

###### 7.8 使用 *textContent* 删除标记并返回所有子 *Text* 节点

###### 7.9 *textContent* 和 *innerText* 的区别

###### 7.10 使用 *normalize()* 合并兄弟 *Text* 节点为一个文本节点

###### 7.11 使用 *splitText()* 拆分文本节点

##### 第八章 - DocumentFragment 节点

###### 8.1 *DocumentFragment* 对象概述

###### 8.2 使用 *createDocumentFragment()* 创建 *DocumentFragment*

###### 8.3 将 *DocumentFragment* 添加到实时 DOM 中

###### 8.4 在 *documentFragment* 上使用 *innerHTML*

###### 8.5 通过克隆将包含节点的片段保留在内存中

##### 第九章 - CSS 样式表和 CSS 规则

###### 9.1 CSS 样式表概述

###### 9.2 访问 DOM 中的所有样式表（即 *CSSStylesheet* 对象）

###### 9.3 *CSSStyleSheet* 属性和方法

###### 9.4 *CSSStyleRule* 概述

###### 9.5 *CSSStyleRule* 属性和方法

###### 9.6 获取样式表中的 CSS 规则列表使用 *CSSRules*

###### 9.7 使用 *.insertRule()* 和 *.deleteRule()* 在样式表中插入和删除 CSS 规则

###### 9.8 使用 *.style* 属性编辑 *CSSStyleRule* 的值

###### 9.9 创建新的内联 CSS 样式表

###### 9.10 以编程方式向 HTML 文档添加外部样式表

###### 9.11 使用 *disabled* 属性禁用/启用样式表

##### 第十章 - DOM 中的 JavaScript

###### 10.1 插入和执行 JavaScript 概述

###### 10.2 JavaScript 默认同步解析

###### 10.3 使用 *defer* 推迟下载和执行外部 JavaScript

###### 10.4 使用 *async* 异步下载和执行外部 JavaScript 文件

###### 10.5 使用动态 *<script>* 强制异步下载和解析外部 JavaScript

###### 10.6 使用 *onload* 回调来异步加载 *<script>*，以便知道何时加载完成

###### 10.7 要注意在 HTML 中 *<script>* 的放置以进行 DOM 操作

###### 10.8 获取 DOM 中 *<script>* 列表

##### 第十一章 - DOM 事件

###### 11.1 DOM 事件概述

###### 11.2 DOM 事件类型

###### 11.3 事件流

###### 11.4 为 *Element* 节点、*window* 对象和 *Document* 对象添加事件监听器

###### 11.5 移除事件监听器

###### 11.6 从事件对象中获取事件属性

###### 11.7 使用 *addEventListener()* 时的 *this* 值

###### 11.8 引用事件的 *target* 而不是事件被调用的节点或对象

###### 11.9 使用 *preventDefault()* 取消默认浏览器事件

###### 11.10 使用 *stopPropagation()* 停止事件流

###### 11.11 使用 *stopImmediatePropagation()* 停止事件流以及同一目标上的其他类似事件

###### 11.12 自定义事件

###### 11.13 模拟/触发鼠标事件

###### 11.14 事件委托

##### 第十二章 - 创建 dom.js - 一个受 jQuery 启发的现代浏览器 DOM 库

###### 12.1 dom.js 概述

###### 12.2 创建一个独特的作用域

###### 12.3 创建 *dom()* 和 *GetOrMakeDom()* 函数，将 *dom()* 和 *GetOrMakeDom.prototype* 暴露给全局范围

###### 12.4 创建传递给 *dom()* 的可选上下文参数

###### 12.5 根据 *params* 基于 DOM 节点引用填充对象并返回对象

###### 12.6 创建 *each()* 方法并使其成为可链式调用的方法

###### 12.7 创建 *html()*、*append()* 和 *text()* 方法

###### 12.8 试用 dom.js

###### 12.9 摘要 & 继续使用 dom.js
