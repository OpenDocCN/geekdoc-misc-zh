# 第八章 - DocumentFragment 节点

## 8.1 *DocumentFragment* 对象概述

创建和使用*DocumentFragment*节点提供了一个轻量级的文档 DOM，它是外部的实时 DOM 树。将*DocumentFragment*视为一个空的文档模板，它的行为就像实时 DOM 树一样，但只存在于内存中，其子节点可以在内存中轻松操作，然后附加到实时 DOM 中。

## 8.2 使用*createDocumentFragment()*创建*DocumentFragment*

在下面的代码中，使用*createDocumentFragment()*创建了一个*DocumentFragment*，并向片段附加了*<li>*。

实时代码：[`jsfiddle.net/domenlightenment/6e3uX`](http://jsfiddle.net/domenlightenment/6e3uX)

```
<!DOCTYPE html>
<html lang="en">
<body>

<script>

var docFrag = document.createDocumentFragment();

["blue", "green", "red", "blue", "pink"].forEach(function(e) {
    var li = document.createElement("li");
    li.textContent = e;
    docFrag.appendChild(li);
});

console.log(docFrag.textContent); *//logs bluegreenredbluepink*

</script>
</body>
</html>

```

当将*documentFragment*用于在内存中创建节点结构时，当将*documentFragment*注入到实时节点结构中时，效率非常高。

你可能会想知道使用*documentFragment*相对于简单地在内存中创建（通过*createElement()*）一个*<div>*并在其中工作以创建 DOM 结构的优势是什么。以下是区别。

+   一个文档片段可以包含任何类型的节点（除了*<body*>或*<html>*），而元素则不行

+   当附加片段时，片段本身并不会添加到 DOM 中。节点的内容会被添加。与附加元素节点不同，其中元素本身是附加的一部分。

+   当将文档片段附加到 DOM 时，它会从文档片段转移到其附加的位置。它不再存在于创建它的地方的内存中。对于暂时用于包含节点并随后移动到实时 DOM 的元素节点，这并不成立。

## 8.3 将*DocumentFragment*添加到实时 DOM

通过将*appendChild()*和*insertBefore()*节点方法传递一个*documentFragment*参数，*documentFragment*的子节点将作为子节点传输到调用这些方法的 DOM 节点上。下面我们创建一个*documentfragment*，向其中添加一些*<li>*，然后使用*appendChild()*将这些新元素节点附加到实时 DOM 树中。

实时代码：[`jsfiddle.net/domenlightenment/Z2LpU`](http://jsfiddle.net/domenlightenment/Z2LpU)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul></ul>

<script>

var ulElm = document.queryselector('ul');
var docFrag = document.createDocumentFragment();

["blue", "green", "red", "blue", "pink"].forEach(function(e) {
    var li = document.createElement("li");
    li.textContent = e;
    docFrag.appendChild(li);
});

ulElm.appendChild(docFrag);

*//logs <ul><li>blue</li><li>green</li><li>red</li><li>blue</li><li>pink</li></ul>*
console.log(document.body.innerHTML);

</script>
</body>
</html>

```

### 注意

作为插入节点方法的参数传递的文档片段将插入整个子节点结构，忽略文档片段节点本身。

## 8.4 在*documentFragment*上使用*innerHTML*

使用节点方法在内存中创建 DOM 结构可能会冗长而费力。一个解决方法是创建一个*documentFragment*，向该片段附加一个*<div>*，因为*innerHTML*不能在文档片段上工作，然后使用*innerHTML*属性使用 HTML 字符串更新片段。通过这样做，可以从 HTML 字符串中构建 DOM 结构。在下面的代码中，我构建了一个 DOM 结构，然后将其视为节点树，而不仅仅是 JavaScript 字符串。

实时代码：[`jsfiddle.net/domenlightenment/4W9sH`](http://jsfiddle.net/domenlightenment/4W9sH)

```
<!DOCTYPE html>
<html lang="en">
<body>

<script>

*//create a <div> and document fragment*
var divElm = document.createElement('div');
var docFrag = document.createDocumentFragment();

*//append div to document fragment*
docFrag.appendChild(divElm);

*//create a DOM structure from a string*
docFrag.querySelector('div').innerHTML = '<ul><li>foo</li><li>bar</li></ul>';

*//the string becomes a DOM structure I can call methods on like querySelectorAll()*
*//Just don't forget the DOM structure is wrapped in a <div>*
console.log(docFrag.querySelectorAll('li').length); *//logs 2*

</script>
</body>
</html>

```

当需要附加使用*documentFragment*和*<div>*创建的 DOM 结构时，您将希望附加结构，跳过*<div>*的注入。

实时代码：[`jsfiddle.net/domenlightenment/kkyKJ`](http://jsfiddle.net/domenlightenment/kkyKJ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div></div>

<script>

*//create a <div> and document fragment*
var divElm = document.createElement('div');
var docFrag = document.createDocumentFragment();

*//append div to document fragment*
docFrag.appendChild(divElm);

*//create a DOM structure from a string*
docFrag.querySelector('div').innerHTML = '<ul><li>foo</li><li>bar</li></ul>';

*//append, starting with the first child node contained inside of the <div>*
document.querySelector('div').appendChild(docFrag.querySelector('div').firstChild);

*//logs <ul><li>foo</li><li>bar</li></ul>*
console.log(document.querySelector('div').innerHTML);

</script>
</body>
</html>

```

### 注意

除了*DocumentFragment*，我们还有*[DOMParser](http://html5.org/specs/dom-parsing.html#domparser)*可以期待。*DOMParser*可以将存储在字符串中的 HTML 解析为 DOM [Document](https://developer.mozilla.org/en/DOM/document "document")。截至今天，它仅在 Opera 和 Firefox 中受支持，但有一个[polyfill](https://gist.github.com/1129031)可用。当然，如果您需要一个独立的 HTML 到 DOM 脚本，请尝试[domify](https://github.com/component/domify)。

## 8.5 离开包含节点的片段，通过克隆在内存中

当附加*documentFragment*时，片段中包含的节点从片段移动到您要附加的结构中。为了将片段的内容保留在内存中，使得节点在附加后仍然存在，只需在附加时使用*cloneNode()*克隆*documentFragment*。在下面的代码中，我克隆了*<li>*而不是从文档片段中传输*<li>*。

*<li>*，保持*<li>*在*documentFragment*节点内存中被克隆。

实时代码：[`jsfiddle.net/domenlightenment/bcJGS`](http://jsfiddle.net/domenlightenment/bcJGS)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul></ul>

<script>
 *//create ul element and document fragment*
var ulElm = document.querySelector('ul');
var docFrag = document.createDocumentFragment();

*//append li's to document fragment*
["blue", "green", "red", "blue", "pink"].forEach(function(e) {
    var li = document.createElement("li");
    li.textContent = e;
    docFrag.appendChild(li);
});

*//append cloned document fragment to ul in live DOM*
ulElm.appendChild(docFrag.cloneNode(true));

*//logs <li>blue</li><li>green</li><li>red</li><li>blue</li><li>pink</li>*
console.log(document.querySelector('ul').innerHTML);

*//logs [li,li,li,li,li]* 
console.log(docFrag.childNodes);

</script>
</body>
</html>

```
