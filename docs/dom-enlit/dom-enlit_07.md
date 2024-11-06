# 第二章 - 文档节点

## 2.1  *document*  节点概述

*HTMLDocument* 构造函数（继承自 *document*）在实例化时具体表示 DOM 中的 *DOCUMENT_NODE*（即 *window.document*）。要验证这一点，我们只需询问在创建 *document* 节点对象时使用了哪个构造函数。

实时代码：[`jsfiddle.net/domenlightenment/qRAzL`](http://jsfiddle.net/domenlightenment/qRAzL)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

console.log(window.document.constructor); *//logs function HTMLDocument() { [native code] }*
console.log(window.document.nodeType); *//logs 9, which is a numeric key mapping to DOCUMENT_NODE*

</script>
</body>
</html>

```

上面的代码得出结论，*HTMLDocument* 构造函数构造了 *window.document* 节点对象，而这个节点是一个 *DOCUMENT_NODE* 对象。

### 注意

当加载 HTML 文档时，通常浏览器会实例化 *Document* 和 *HTMLDocument* 构造函数。然而，使用 *document.implementation.createHTMLDocument()* 可以在当前加载到浏览器中的 HTML 文档之外创建自己的 HTML 文档。除了 *createHTMLDocument()* 外，还可以使用 *createDocument()* 创建尚未设置为 HTML 文档的文档对象。通常，这些方法的使用与以编程方式向 iframe 提供 HTML 文档相关。

## 2.2 *HTMLDocument* 属性和方法（包括继承的）

要获取有关 *HTMLDocument* 节点上可用属性和方法的准确信息，最好忽略规范，并询问浏览器有哪些可用。检查下面代码中创建的数组，详细说明了从 *HTMLDocument* 节点（也称为 *window.document*）对象中可用的属性和方法。

实时代码：[`jsfiddle.net/domenlightenment/jprPe`](http://jsfiddle.net/domenlightenment/jprPe)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

*//document own properties*
console.log(Object.keys(document).sort());

*//document own properties & inherited properties*
var documentPropertiesIncludeInherited = [];
for(var p in document){
	documentPropertiesIncludeInherited.push(p);
}
console.log(documentPropertiesIncludeInherited.sort());

*//documment inherited properties only*
var documentPropertiesOnlyInherited = [];
for(var p in document){
	if(
		!document.hasOwnProperty(p)){documentPropertiesOnlyInherited.push(p);
	}
}
console.log(documentPropertiesOnlyInherited.sort());

</script>
</body>
</html>

```

即使不考虑继承的属性，可用的属性仍然很多。下面我手动挑选了一些值得注意的属性和方法列表，以便在本章的上下文中使用。

+   *doctype*

+   *documentElement*

+   *implementation*.*

+   *activeElement*

+   *body*

+   *head*

+   *title*

+   *lastModified*

+   *referrer*

+   *URL*

+   *defaultview*

+   *compatMode*

+   *ownerDocument*

+   *hasFocus()*

### 注意

*HTMLDocument* 节点对象用于访问（通常继承）许多用于处理 DOM 的方法和属性（例如 *document.querySelectorAll()*）。你将看到许多这些属性在本章未讨论的属性在接下来的适当章节中讨论。

## 2.3 获���一般 HTML 文档信息（标题、URL、引用者、最后修改时间、compatMode）

*document* 对象提供了有关正在加载的 HTML 文档/DOM 的一些常规信息。在下面的代码中，我使用 *document.title*、*document.URL*、*document.referrer*、*document.lastModified* 和 *document.compatMode* 属性来获取有关 *document* 的一些常规信息。根据属性名称，返回的值应该是明显的。

实时代码：[`jsfiddle.net/domenlightenment/pX8Le`](http://jsfiddle.net/domenlightenment/pX8Le)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

var d = document;
console.log('title = ' +d.title);
console.log('url = ' +d.URL);
console.log('referrer = ' +d.referrer);
console.log('lastModified = ' +d.lastModified);

*//logs either BackCompat (Quirks Mode) or CSS1Compat (Strict Mode)*
console.log('compatibility mode = ' +d.compatMode);

</script>
</body>
</html>

```

## 2.4 *document* 子节点

*文档* 节点可以包含一个 *DocumentType* 节点对象和一个 *Element* 节点对象。这不应该让人感到意外，因为 HTML 文档通常只包含一个 doctype（例如 *<!DOCTYPE html>*）和一个元素（例如 *<html lang="en">*）。因此，如果您请求 *Document* 对象的子节点（例如 *document.childNodes*），您将得到一个数组，其中至少包含文档的 doctype/DTD 和 *<html lang="en">* 元素。下面的代码展示了 *window.document* 是一种节点对象（即 *Document*）并具有子节点。

实时代码：[`jsfiddle.net/domenlightenment/UasKc`](http://jsfiddle.net/domenlightenment/UasKc)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>
 *//This is the doctype/DTD*
console.log(document.childNodes[0].nodeType); *//logs 10, which is a numeric key mapping to DOCUMENT_TYPE_NODE*

*//This is the <html> element*
console.log(document.childNodes[1].nodeType); *//logs 1, which is a numeric key ***mapping to*** ELEMENT_TYPE_NODE*

</script>
</body>
</html>

```

### 注：

不要混淆从 *HTMLDocument* 构造函数创建的 *window.document* 对象与 *Document* 对象。只需记住 *window.document* 是 DOM 接口的起始点。这就是为什么 *document.childNodes* 包含子节点的原因。

如果在 *<html lang="en">* 元素之外创建了注释节点（本书未讨论），它将成为 *window.document* 的子节点。然而，在 *<html>* 元素之外存在注释节点可能会导致 IE 中的一些错误结果，并且也违反了 DOM 规范。

## 2.5 *文档* 提供了 *<!DOCTYPE>*、*<html lang="en">*、*<head>* 和 *<body>* 的快捷方式。

使用下面列出的属性，我们可以快捷地引用以下节点：

+   *document.doctype* 指的是 *<!DOCTYPE>*

+   *document.documentElement* 指的是 *<html lang="en">*

+   *document.head* 指的是 *<head>*

+   *document.body* 指的是 *<body>*

下面的代码演示了这一点。

实时代码：[`jsfiddle.net/domenlightenment/XsSTM`](http://jsfiddle.net/domenlightenment/XsSTM)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>
 *console.log(document.**doctype**); *// logs DocumentType {nodeType=10, ownerDocument=document, ...}*

console.log(document.**documentElement**); *// logs <html lang="en">*

console.log(document.**head**); *// logs <head>*

console.log(document.**body**); *// logs <body>*

</script>

</body>
</html>* 
```

*### 注：

doctype 或 DTD 是 10 或 *DOCUMENT_TYPE_NODE* 的 *nodeType*，不应与 *DOCUMENT_NODE*（也称为 *window.document* 从 *HTMLDocument()* 构造）混淆。doctype 是使用 *DocumentType()* 构造函数构造的。

在 Safari、Chrome 和 Opera 中，*document.doctype* 不会出现在 *document.childNodes* 列表中。

## 2.6 使用 *document.implementation.hasFeature()* 检测 DOM 规范/功能

可以使用 *document.implementation.hasFeature()* 来询问（布尔值）当前文档所实现/支持的功能和级别。例如，我们可以通过向 *hasFeature()* 方法传递功能名称和版本来询问浏览器是否已经实现了核心 DOM 3.0 规范。在下面的代码中，我询问浏览器是否已经实现了核心 2.0 和 3.0 规范。

实时代码：[`jsfiddle.net/domenlightenment/TYYZ6`](http://jsfiddle.net/domenlightenment/TYYZ6)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

console.log(document.implementation.hasFeature('Core','2.0')); *console.log(document.**implementation.hasFeature**('Core','3.0')); *</script>
</body>
</html>** 
```

**以下表格定义了您可以传递给 *hasFeature()* 方法的功能（[规范将这些称为模块](http://www.w3.org/TR/DOM-Level-2-Core/introduction.html#ID-Conformance)）和版本。

| 功能 | 支持的版本 |
| --- | --- |
| 核心 | 1.0, 2.0, 3.0 |
| XML | 1.0, 2.0, 3.0 |
| HTML | 1.0, 2.0 |
| 视图 | 2.0 |
| 样式表 | 2.0 |
| CSS | 2.0 |
| CSS2 | 2.0 |
| 事件 | 2.0, 3.0 |
| UI 事件 | 2.0, 3.0 |
| 鼠标事件 | 2.0, 3.0 |
| 变动事件 | 2.0, 3.0 |
| HTML 事件 | 2.0 |
| 范围 | 2.0 |
| 遍历 | 2.0 |
| LS（在文件和 DOM 树之间同步加载和保存） | 3.0 |
| LS-Asnc（异步在文件和 DOM 树之间加载和保存） | 3.0 |
| 验证 | 3.0 |

### 注释

不要仅仅信任*hasFeature()*，您还应该使用[能力检测](http://dev.opera.com/articles/view/using-capability-detection/)以及*hasFeature()*。

使用*isSupported*方法实现可以仅针对特定/选定的节点（即*element.isSupported(feature,version*）收集信息。

您可以通过访问[`www.w3.org/2003/02/06-dom-support.html`](http://www.w3.org/2003/02/06-dom-support.html)来确定用户代理支持的内容。在这里，您将找到一个表，指示加载 URL 的浏览器声称实现了什么。

## 2.7 获取*文档*中焦点/活动节点的引用

使用*document.activeElement*，我们可以快速获取文档中具有焦点/活动状态的节点的引用。在下面的代码中，在页面加载时，我将文档的焦点设置为*<textarea>*节点，然后使用*activeElement*属性获取对该节点的引用。

实时代码：[`jsfiddle.net/domenlightenment/N9npb`](http://jsfiddle.net/domenlightenment/N9npb)

```
<!DOCTYPE html>
<html lang="en">
<body>
<textarea></textarea>

<script>

*//set focus to <textarea>*
document.querySelector('textarea').focus();

*​//get reference to element that is focused/active in the document*
console.log(document.activeElement); *//logs <textarea>*

</script>
</body>
</html>

```

### 注释

聚焦/活动元素返回具有聚焦能力的元素。如果您在浏览器中访问网页并开始按下 Tab 键，您将看到焦点从一个可以获得焦点的元素转移到页面中的另一个元素。不要将节点的选择（用鼠标突出显示 HTML 页面的部分）与为输入某些内容而获得焦点的元素混淆，可以使用按键、空格键或鼠标。

## 2.8 确定*文档*或*文档*内的任何节点是否具有焦点

使用 document.hasFocus()方法可以知道用户当前是否专注于加载有 HTML 文档的窗口。在下面的代码中，您会看到，如果我们执行代码然后专注于另一个窗口、标签或应用程序，*getFocus()*将返回 false。

实时代码：[`jsfiddle.net/domenlightenment/JkE3d`](http://jsfiddle.net/domenlightenment/JkE3d)

```
<!DOCTYPE html>
<html lang="en">
<body>

<script> **//If you keep focus on the window/tab that has the document loaded its true. If not it's false.*
setTimeout(function(){console.log(**document.hasFocus(**))},5000); **</script>
</body>
</html>*** 
```

***## 2.9 *document.defaultview*是头部/全局对象的快捷方式

您应该知道*defaultView*属性是 JavaScript head 对象的快捷方式，有些人称之为全局对象。在 Web 浏览器中，head 对象是*window*对象，*defaultView*将指向 JavaScript 浏览器环境中的此对象。下面的代码演示了浏览器中*defaultView*的值。

实时代码：[`jsfiddle.net/domenlightenment/QqK6Q`](http://jsfiddle.net/domenlightenment/QqK6Q)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

console.log(document.defaultView) *//reference, head JS object. Would be window object in a browser.*

</script>
</body>
</html>

```

如果你处理的是一个无头的 DOM 或者一个不在 web 浏览器中运行的 JavaScript 环境（比如 [node.js](http://nodejs.org/)），这个属性可以让你访问到 head 对象作用域。

## 通过 *ownerDocument* 从 *element* 获取 *Document* 的引用 2.9。

当在节点上调用 *ownerDocument* 属性时，它会返回节点所包含的 *Document* 的引用。在下面的代码中，我获取了 HTML 文档中 *<body>* 的 *Document* 的引用以及 iframe 中包含的 *<body>* 元素的 *Document* 节点。

内联代码: N/A

```
<!DOCTYPE html>
<html lang="en">
<body>

<iframe src="http://someFileServedFromServerOnSameDomain.html"></iframe>

<script>

*//get the window.document that the <body> is contained within*
console.log(document.body.ownerElement);

*//get the window.document the <body> inside of the iframe is contained within*
console.log(window.frames[0].document.body.ownerElement);

</script>
</body>
</html>
```

如果在 *Document* 节点上调用 *ownerDocument*，则返回的值为 *null*。
