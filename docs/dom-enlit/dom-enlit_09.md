# 第四章 - 元素节点选择

## 4.1 选择特定的元素节点

获取单个元素节点的最常见方法有：

+   *querySelector()*

+   *getElementById()*

在下面的代码中，我利用这两种方法来从 HTML 文档中选择一个元素节点。

实时代码：[`jsfiddle.net/domenlightenment/b4Rch`](http://jsfiddle.net/domenlightenment/b4Rch)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul>
<li>Hello</li>
<li>big</li>
<li>bad</li>
<li id="last">world</li>
</ul>

<script>

console.log(document.querySelector('li').textContent); *//logs Hello*
console.log(document.getElementById('last').textContent); *//logs world*

</script>
</body>
</html>

```

*getElementById()*方法相对于更强大的*querySelector()*方法来说相当简单。*querySelector()*方法允许以[CSS 选择器语法](http://www.w3.org/TR/css3-selectors/#selectors)的形式传递参数。基本上，你可以传递一个 CSS 3 选择器（例如*'#score>tbody>tr>td:nth-of-type(2)'*），它将用于在 DOM 中选择单个元素。

### 注意

*querySelector()*会根据选择器在文档中找到的第一个节点元素。例如，在上面的代码示例中，我们传递了一个选择器，该选择器将选择所有的 li 元素，但只返回第一个。

*querySelector()*也在元素节点上定义。这允许该方法将结果限制在 DOM 树的特定部分（允许上下文查询）。

## 4.2 选择/创建元素节点列表（也称为*NodeList*）

在 HTML 文档中选择/创建节点列表的最常见方法有：

+   *querySelectorAll()*

+   *getElementsByTagName()*

+   *getElementsByClassName()*

在下面，我们使用这三种方法来创建文档中*<li>*元素的列表。

实时代码：[`jsfiddle.net/domenlightenment/nT7Lr`](http://jsfiddle.net/domenlightenment/nT7Lr)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul>
<li class="liClass">Hello</li>
<li class="liClass">big</li>
<li class="liClass">bad</li>
<li class="liClass">world</li>
</ul>

<script>

*//all of the methods below create/select the same list of <li> elements from the DOM*
console.log(document.querySelectorAll('li'));
console.log(document.getElementsByTagName('li'));
console.log(document.getElementsByClassName('liClass'));

</script>
</body>
</html>

```

如果在上面的代码示例中使用的方法没有选择特定元素的清晰，而是创建了一个元素列表（也称为[*NodeLists*](https://developer.mozilla.org/En/DOM/NodeList)），你可以从中选择元素。

### 注意

从*getElementsByTagName()*和*getElementsByClassName()*创建的*NodeLists*被认为是动态的，即使在创建/选择列表后更新文档，它们也会始终反映文档的状态。

*querySelectorAll()*方法不会返回一个动态的元素列表。这意味着从*querySelectorAll()*创建的列表是在创建时对文档的快照，不会随着文档的更改而变化。该列表是静态的，不是动态的。

*querySelectorAll()*、*getElementsByTagName()*和*getElementsByClassName*也在元素节点上定义。这允许该方法将结果限制在 DOM 树的特定部分（例如*document.getElementById('header').getElementsByClassName('a')*）。

我没有提到*getElementsByName()*方法，因为它不常用于其他解决方案，但你应该知道它的存在，用于从具有相同名称属性值的文档中选择表单、img、frame、embed 和 object 元素。

传递给 *querySelectorAll()* 或 *getElementsByTagName()* 字符串 *'*'*，通常表示全部，将返回文档中所有元素的列表。

记住，*childNodes* 会返回一个 *NodeList*，就像 *querySelectorAll()*、*getElementsByTagName()* 和 *getElementsByClassName* 一样。

*NodeLists* 类似于数组（但不继承数组方法）的列表/集合，并且具有只读的 *length* 属性

## 4.3 选择所有立即子元素节点

使用元素节点的 *children* 属性，我们可以得到一个（又名 [*HTMLCollection*](https://developer.mozilla.org/en/DOM/HTMLCollection)）包含所有立即子节点的元素节点的列表。在下面的代码中，我使用 *children* 来创建一个包含所有在 *<ul>* 中的 *<li>* 的选择/列表。

实时代码：[`jsfiddle.net/domenlightenment/svfRC`](http://jsfiddle.net/domenlightenment/svfRC)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul>
<li><strong>Hi</strong></li>
<li>there</li>
</ul>

<script>

var ulElement = document.querySelector('ul').children;

*//logs a list/array of all immediate child element nodes*
console.log(ulElement); *//logs [<li>, <li>]*

</script>
</body>
</html>

```

注意，只使用 *children* 仅会给我们返回立即元素节点，排除了任何不是元素的节点（例如文本节点）。如果元素没有子元素，则 *children* 将返回一个空的类似数组的列表。

### 注意事项

*HTMLCollection* 包含按文档顺序排列的元素，也就是说它们按照它们在 DOM 中出现的顺序放置在数组中。

*HTMLCollection* 是动态的，这意味着对文档的任何更改都会动态地反映在集合中。

## 4.4 上下文元素选择

*querySelector()*、*querySelectorAll()*、*getElementsByTagName()* 和 *getElementsByClassName* 这些通常从 *document* 对象访问的方法也在元素节点上定义了。这允许这些方法将结果限制在 DOM 树的特定分支上。换句话说，你可以通过在元素节点对象上调用这些方法来选择你想要这些方法在其中搜索元素节点的特定上下文。

实时代码：[`jsfiddle.net/domenlightenment/fL6tV`](http://jsfiddle.net/domenlightenment/fL6tV)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>
<ul>
<li class="liClass">Hello</li>
<li class="liClass">big</li>
<li class="liClass">bad</li>
<li class="liClass">world</li>
</ul>
</div>

<ul>
<li class="liClass">Hello</li>
</ul>

<script>

*//select a div as the context to run the selecting methods only on the contents of the div*
var div = document.querySelector('div');

console.log(div.querySelector('ul'));
console.log(div.querySelectorAll('li'));
console.log(div.getElementsByTagName('li'));
console.log(div.getElementsByClassName('liClass'));

</script>
</body>
</html>

```

这些方法不仅适用于 live dom，还适用于在代码中创建的编程 DOM 结构。

实时代码：[`jsfiddle.net/domenlightenment/CCnva`](http://jsfiddle.net/domenlightenment/CCnva)

```
<!DOCTYPE html>
<html lang="en">
<body>

<script>
 *//create DOM structure*
var divElm = document.createElement('div');
var ulElm = document.createElement('ul');
var liElm = document.createElement('li');
liElm.setAttribute('class','liClass');
ulElm.appendChild(liElm);
divElm.appendChild(ulElm);

*//use selecting methods on DOM structure*
console.log(divElm.querySelector('ul'));
console.log(divElm.querySelectorAll('li'));
console.log(divElm.getElementsByTagName('li'));
console.log(divElm.getElementsByClassName('liClass'));

</body>
</html>

```

## 4.5 元素节点的预配置选择/列表

你应该知道，有一些遗留的、预配置的类似数组的列表，包含了来自 HTML 文档的元素节点。下面我列出了一些（不是完整的列表），可能对你有所帮助。

+   *document.all* - HTML 文档中的所有元素

+   *document.forms* - HTML 文档中的所有 *<form>* 元素

+   *document.images* - HTML 文档中的所有 *<img>* 元素

+   *document.links* - HTML 文档中的所有 *<a>* 元素

+   *document.scripts* - HTML 文档中的所有 *<script>* 元素

+   *document.styleSheets* - HTML 文档中的所有 *<link>* 或 *<style>* 对象

### 注意事项

这些预配置的数组是从 [HTMLCollection](https://developer.mozilla.org/en/DOM/HTMLCollection) 接口/对象构建的，除了 *document.styleSheets*，它使用的是 *StyleSheetList*

*[HTMLCollection](https://developer.mozilla.org/zh-CN/docs/Web/API/HTMLCollection)*和*[NodeList](https://developer.mozilla.org/zh-CN/docs/Web/API/NodeList)*一样是动态的。

奇怪的是*document.all*是由*HTMLAllCollection*而不是*HTMLCollection*构造的，并且在 Firefox 中不受支持。

## 4.6 使用*matchesSelector()*验证元素是否被选中。

使用*matchesSelector()*方法，我们可以确定元素是否匹配选择器字符串。例如，假设我们想要确定一个*<li>*是否是*<ul>*的第一个子元素。在下面的代码示例中，我选择了*<ul>*中的第一个*<li>*，然后询问该元素是否匹配选择器*li:first-child*。因为实际上是这样的，所以*matchesSelector()*方法返回*true*。

在线代码：[`jsfiddle.net/domenlightenment/9RayM`](http://jsfiddle.net/domenlightenment/9RayM)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul>
<li>Hello</li>
<li>world</li>
</ul>

<script>

*//fails in modern browser must use browser prefix moz, webkit, o, and ms*
console.log(document.querySelector('li').matchesSelector('li:first-child')); *//logs false

//prefix moz
//console.log(document.querySelector('li').**mozMatchesSelector**('li:first-child'));

//prefix webkit
//console.log(document.querySelector('li').**webkitMatchesSelector**('li:first-child'));

//prefix o
//console.log(document.querySelector('li').**oMatchesSelector**('li:first-child'));

//prefix ms
//console.log(document.querySelector('li').**msMatchesSelector**('li:first-child'));*

</script>
</body>
</html>

```

### 注意

matchesSelector 在浏览器中的使用情况并不乐观，因为它的使用方式落后于浏览器前缀*mozMatchesSelector()*、*webkitMatchesSelector()*、*oMatchesSelector()*、*msMatchesSelector()*。

将来*matchesSelector()*将被重命名为*matches()*。
