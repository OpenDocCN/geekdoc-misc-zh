# 第三章 - 元素节点

## 3.1 *HTML*Element* 对象概述

HTML 文档中的元素都具有独特的特性，因此它们都有一个独特的[JavaScript 构造函数](http://www.w3.org/TR/2003/REC-DOM-Level-2-HTML-20030109/html.html)，用于将元素实例化为 DOM 树中的节点对象。例如，*<a>* 元素是从 *HTMLAnchorElement()* 构造函数创建的 DOM 节点。下面我们验证了锚元素是否是从 *HTMLAnchorElement()* 创建的。

内联代码：[`jsfiddle.net/domenlightenment/TgcNu`](http://jsfiddle.net/domenlightenment/TgcNu)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a></a>

<script>
 *// grab <a> element node from DOM and ask for the name of the constructor that constructed it*
console.log(document.querySelector('a').constructor);
*//logs function HTMLAnchorElement() { [native code] }*

</script>
</body>
</html>

```

我在前面的代码示例中试图表达的观点是，DOM 中的每个元素都是由唯一的 JavaScript 接口/构造函数构造而成的。下面的列表（不是[完整列表](http://www.whatwg.org/specs/web-apps/current-work/multipage/section-index.html#elements-1)）应该能让你对用于创建 HTML 元素的接口/构造函数有一个很好的理解。

+   *HTMLHtmlElement*

+   *HTMLHeadElement*

+   *HTMLLinkElement*

+   *HTMLTitleElement*

+   *HTMLMetaElement*

+   *HTMLBaseElement*

+   *HTMLIsIndexElement*

+   *HTMLStyleElement*

+   *HTMLBodyElement*

+   *HTMLFormElement*

+   *HTMLSelectElement*

+   *HTMLOptGroupElement*

+   *HTMLOptionElement*

+   *HTMLInputElement*

+   *HTMLTextAreaElement*

+   *HTMLButtonElement*

+   *HTMLLabelElement*

+   *HTMLFieldSetElement*

+   *HTMLLegendElement*

+   *HTMLUListElement*

+   *HTMLOListElement*

+   *HTMLDListElement*

+   *HTMLDirectoryElement*

+   *HTMLMenuElement*

+   *HTMLLIElement*

+   *HTMLDivElement*

+   *HTMLParagraphElement*

+   *HTMLHeadingElement*

+   *HTMLQuoteElement*

+   *HTMLPreElement*

+   *HTMLBRElement*

+   *HTMLBaseFontElement*

+   *HTMLFontElement*

+   *HTMLHRElement*

+   *HTMLModElement*

+   *HTMLAnchorElement*

+   *HTMLImageElement*

+   *HTMLObjectElement*

+   *HTMLParamElement*

+   *HTMLAppletElement*

+   *HTMLMapElement*

+   *HTMLAreaElement*

+   *HTMLScriptElement*

+   *HTMLTableElement*

+   *HTMLTableCaptionElement*

+   *HTMLTableColElement*

+   *HTMLTableSectionElement*

+   *HTMLTableRowElement*

+   *HTMLTableCellElement*

+   *HTMLFrameSetElement*

+   *HTMLFrameElement*

+   *HTMLIFrameElement*

请记住，上述每个 *HTML*Element* 都继承自 *HTMLElement*、*Element*、*Node* 和 *Object* 的属性和方法。

## 3.2 *HTML*Element* 对象的属性和方法（包括继承的）

要获取关于 *HTML*Element* 节点可用属性和方法的准确信息，最好忽略规范，并询问浏览器有哪些可用。查看下面代码中创建的数组，详细说明了来自 HTML 元素节点的属性和方法。

内联代码：[`jsfiddle.net/domenlightenment/vZUHw`](http://jsfiddle.net/domenlightenment/vZUHw)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href="#">Hi</a>

<script>

var anchor = document.querySelector('a');

*//element own properties*
console.log(Object.keys(anchor).sort());

*//element own properties & inherited properties*
var documentPropertiesIncludeInherited = [];
for(var p in document){
	documentPropertiesIncludeInherited.push(p);
}
console.log(documentPropertiesIncludeInherited.sort());

*//element inherited properties only*
var documentPropertiesOnlyInherited = [];
for(var p in document){
	if(!document.hasOwnProperty(p)){
		documentPropertiesOnlyInherited.push(p);
	}
}
console.log(documentPropertiesOnlyInherited.sort());

</script>
</body>
</html>

```

即使不考虑继承的属性，可用的属性也很多。下面我手工挑选了一些值得注意的属性和方法列表（包括继承的）以供本章节的上下文参考。

+   *createElement()*

+   *tagName*

+   *children*

+   *getAttribute()*

+   *setAttribute()*

+   *hasAttribute()*

+   *removeAttribute()*

+   *classList()*

+   *dataset*

+   *attributes*

要查看完整列表，请查阅 MDN 文档，其中涵盖了大多数 HTML 元素可用的 [一般属性和方法](https://developer.mozilla.org/en/DOM/element)。

## 3.3 创建元素

当浏览器解释 HTML 文档并基于文档内容构建相应的 DOM 时，*Element* 节点会被实例化。在此之后，也可以使用 *createElement()* 来编程创建 *Element* 节点。在下面的代码中，我创建了一个 *<textarea>* 元素节点，然后将该节点注入到实时 DOM 树中。

live code: [`jsfiddle.net/domenlightenment/d3Yvv`](http://jsfiddle.net/domenlightenment/d3Yvv)

```
<!DOCTYPE html>
<html lang="en">
<body>
<script>

var elementNode = document.createElement('textarea'); *//HTMLTextAreaElement() constructs <textarea>*
document.body.appendChild(elementNode);

console.log(document.querySelector('textarea')); *//verify it's now in the DOM*

</script>
</body>
</html>

```

传递给 *createElement()* 方法的值是一个字符串，指定要创建的元素类型（也称为 *[tagName](http://www.w3.org/TR/2000/REC-DOM-Level-2-Core-20001113/core.html#ID-104682815)*）。

### 注意

传递给 createElement 的值在创建元素之前会被更改为小写字符串。

## 3.4 获取元素的标签名

使用 *tagName* 属性可以访问元素的名称。*tagName* 属性返回与使用 *nodeName* 返回的值相同。无论源 HTML 文档中的大小写如何，两者都返回大写值。

下面我们获取 DOM 中 *<a>* 元素的名称。

live code: [`jsfiddle.net/domenlightenment/YJb3W`](http://jsfiddle.net/domenlightenment/YJb3W)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href="#">Hi</a>

<script>

console.log(document.querySelector('a').tagName); *//logs A*

*//the nodeName property returns the same value*
console.log(document.querySelector('a').nodeName); *//logs A*

</script>
</body>
</html>

```

## 3.5 获取元素属性和值的列表/集合

使用 *attributes* 属性（从 *Node* 继承给元素节点）可以获取元素当前定义的 *[Attr](http://www.w3.org/TR/DOM-Level-3-Core/core.html#ID-637646024)* 节点的集合。返回的列表是一个 *[NameNodeMap](https://developer.mozilla.org/en/DOM/NamedNodeMap)*。下面我循环遍历属性集合，暴露集合中包含的每个 *Attr* 节点对象。

live code: [`jsfiddle.net/domenlightenment/9gVQf`](http://jsfiddle.net/domenlightenment/9gVQf)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href='#' title="title" data-foo="dataFoo" class="yes" style="margin:0;" foo="boo"></a>

<script>

var atts = document.querySelector('a').attributes;

for(var i=0; i< atts.length; i++){
	console.log(atts[i].nodeName +'='+ atts[i].nodeValue);
}

</script>
</body>
</html>

```

### 注意

从访问 attributes 属性返回的数组应该被视为活动的。这意味着其内容随时可以更改。

返回的数组继承自 *NameNodeMap*，提供了一些操作数组的方法，如 *getNamtedItem()*、*setNamedItem()* 和 *removeNamedItem()*。使用这些方法操作 *attributes* 应该次于使用 *getAttribute()*、*setAttribute()*、*hasAttribute()*、*removeAttribute()*。作者认为处理 [Attr](http://www.w3.org/TR/DOM-Level-3-Core/core.html#ID-637646024) 节点很混乱。使用 *attributes* 的唯一优点在于其功能性，可以返回一个活动属性列表。

*attributes* 属性是一个类似数组的集合，具有只读的 *length* 属性。

布尔属性（例如 *<option selected>foo</option>*）会显示在 *attributes* 列表中，但除非提供值（例如 *<option selected="selected">foo</option>*），否则没有值。

## 3.6 获取、设置和删除元素的属性值

获取、设置或删除元素 [属性](http://www.whatwg.org/specs/web-apps/current-work/#attributes-1) 值的最一致的方式是使用 *getAttribute()*, *setAttribute()* 和 *removeAttribute()* 方法。在下面的代码中，我演示了管理元素属性的每种方法。

实时代码：[`jsfiddle.net/domenlightenment/wp7rq`](http://jsfiddle.net/domenlightenment/wp7rq)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href='#' title="title" data-foo="dataFoo" style="margin:0;" class="yes" foo="boo" hidden="hidden">#link</a>

<script>

var atts = document.querySelector('a');

*//remove attributes*
atts.removeAttribute('href');
atts.removeAttribute('title');
atts.removeAttribute('style');
atts.removeAttribute('data-foo');
atts.removeAttribute('class');
atts.removeAttribute('foo'); *//custom attribute*
atts.removeAttribute('hidden'); *//boolean attribute*

*//set (really re-set) attributes*
atts.setAttribute('href','#');
atts.setAttribute('title','title');
atts.setAttribute('style','margin:0;');
atts.setAttribute('data-foo','dataFoo');
atts.setAttribute('class','yes');
atts.setAttribute('foo','boo');
atts.setAttribute('hidden','hidden');* //boolean attribute requires sending the attribute as the value too*

*//get attributes*
console.log(atts.getAttribute('href'));
console.log(atts.getAttribute('title'));
console.log(atts.getAttribute('style'));
console.log(atts.getAttribute('data-foo'));
console.log(atts.getAttribute('class'));
console.log(atts.getAttribute('foo'));
console.log(atts.getAttribute('hidden'));

</script>
</body>
</html>

```

### 注释

使用 *removeAttribute()* 而不是使用 *setAttribute()* 将属性值设置为 *null* 或 *''*

一些元素属性可以作为对象属性从元素节点获取（即 *document.body.id* 或 *document.body.className*）。作者建议避免使用这些属性，而是使用 remove、set 和 get 属性方法。

## 3.7 验证元素是否具有特定属性

确定（即布尔）元素是否具有属性的最佳方法是使用 *hasAttribute()* 方法。下面我验证 *<a>* 是否具有 *href*、*title*、*style*、*data-foo*、*class* 和 *foo* 属性。

实时代码：[`jsfiddle.net/domenlightenment/hbCCE`](http://jsfiddle.net/domenlightenment/hbCCE)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href='#' title="title" data-foo="dataFoo" style="margin:0;" class="yes" goo></a>

<script>

var atts = document.querySelector('a');

console.log(
	atts.hasAttribute('href'),
	atts.hasAttribute('title'),
	atts.hasAttribute('style'),
	atts.hasAttribute('data-foo'),
	atts.hasAttribute('class'),
	atts.hasAttribute('goo') *//Notice this is true regardless if a value is defined* 
)

</script>
</body>
</html>

```

即使属性没有值，该方法也会返回 *true*。例如，使用 *hasAttribute()* 我们可以为 [布尔属性](http://www.w3.org/TR/html4/intro/sgmltut.html#h-3.3.4.2) 得到一个布尔值。在下面的代码示例中，我们检查复选框是否被选中。

实时代码：[`jsfiddle.net/domenlightenment/tb6Ja`](http://jsfiddle.net/domenlightenment/tb6Ja)

```
<!DOCTYPE html>
<html lang="en">
<body>

<input type="checkbox" checked></input>

<script>

var atts = document.querySelector('input');

console.log(atts.hasAttribute('checked')); *//logs true*

</script>
</body>
</html>

```

## 3.8 获取类属性值列表

使用元素节点上可用的 *classList* 属性，我们可以访问一个类属性值列表（即 *[DOMTokenList](http://www.w3.org/TR/dom/#interface-domtokenlist)*），这比从 *className* 属性返回的空格分隔的字符串值更容易处理。在下面的代码中，我对比了 *classList* 与 *className* 的使用。

实时代码：[`jsfiddle.net/domenlightenment/DLJEA`](http://jsfiddle.net/domenlightenment/DLJEA)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div class="big brown bear"></div>

<script>

var elm = document.querySelector('div');

console.log(elm.classList); *//big brown bear {0="big", 1="brown", 2="bear", length=3, ...}*
console.log(elm.className); *//logs 'big brown bear'*

</script>
</body>
</html>
```

### 注释

鉴于 *classList* 是类似数组的集合，它有一个只读的 *length* 属性。

*classList* 是只读的，但可以使用 *add()*、*remove()*、*contains()* 和 *toggle()* 方法进行修改

IE9 不支持 *classList*。支持将在 [IE10](http://blogs.msdn.com/b/ie/archive/2012/05/31/windows-release-preview-the-sixth-ie10-platform-preview.aspx) 中出现。有 [几种](https://github.com/eligrey/classList.js) [polyfills](https://gist.github.com/1381839) 可用。

## 3.9 添加和删除类属性的子值

使用 *classList.add()* 和 *classList.remove()* 方法非常简单地编辑类属性的值。在下面的代码中，我演示了添加和删除类值。

实时代码：[`jsfiddle.net/domenlightenment/YVaUU`](http://jsfiddle.net/domenlightenment/YVaUU)

```
<!DOCTYPE html>
<html lang="en">
<body>
<div class="dog"></div>​

<script>

var elm = document.querySelector('div');

elm.classList.add('cat');
elm.classList.remove('dog');
console.log(elm.className); *//'cat'*

</script>
</body>
</html>

```

## 3.10 切换类属性值

使用*classList.toggle()*方法，我们可以切换类属性的子值。这使我们能够在缺失时添加一个值，或者在已经添加时删除一个值。在下面的代码中，我切换了*'visible'*值和*'grow'*值。这实质上意味着我从类属性值中删除*'visible'*并添加*'grow'*。

live code: [`jsfiddle.net/domenlightenment/uFp6J`](http://jsfiddle.net/domenlightenment/uFp6J)

```
<!DOCTYPE html>
<html lang="en">
<body>
<div class="visible"></div>​

<script>

var elm = document.querySelector('div');

elm.classList.toggle('visible');
elm.classList.toggle('grow');
console.log(elm.className); *//'grow'*

</script>
</body>
</html>

```

## 3.11 确定类属性值是否包含特定值

使用*classList.contains()*方法，可以确定（布尔值）类属性值是否包含特定的子值。在下面的代码中，我们测试*<div>*类属性是否包含*brown*的子值。

live code: [`jsfiddle.net/domenlightenment/njyaP`](http://jsfiddle.net/domenlightenment/njyaP)

```
<!DOCTYPE html>
<html lang="en">
<body>
<div class="big brown bear"></div>​

<script>

var elm = document.querySelector('div');

console.log(elm.classList.contains('brown')); *//logs true*

</script>
</body>
</html>

```

## 3.12 获取和设置数据属性*

元素节点的*dataset*属性提供了一个包含以 data-*开头的所有元素属性的对象。因为它只是一个 JavaScript 对象，我们可以操作*dataset*，并使 DOM 中的元素反映这些更改。

live code: [`jsfiddle.net/domenlightenment/ystgj`](http://jsfiddle.net/domenlightenment/ystgj)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div data-foo-foo="foo" data-bar-bar="bar"></div>​

<script>

var elm = document.querySelector('div');

*//get* *console.log(elm.**dataset.fooFoo**); *//logs 'foo'*
console.log(elm.**dataset.barBar**); *//logs 'bar'*

*//set*
**elm.dataset.gooGoo = 'goo';**
console.log(elm.dataset); *//logs DOMStringMap {fooFoo="foo", barBar="bar", gooGoo="goo"}*

*//what the element looks like in the DOM* 
console.log(elm); *//logs <div data-foo-foo="foo" data-bar-bar="bar" data-goo-goo="goo">*

</script>
</body>
</html>* 
```

*### 注意事项

*dataset*包含数据属性的驼峰命名版本。这意味着*data-foo-foo*将在数据集*DOMStringMap*对象的属性*fooFoo*中列出。*-*被驼峰命名替换。

通过在 DOM 上使用*delete*运算符来删除数据-*属性是非常简单的（例如*delete dataset.fooFoo*）

*dataset*在 IE9 中不受支持。有一个[polyfill](https://github.com/remy/polyfills/blob/master/dataset.js)可用。然而，您总是可以使用 getAttribute('data-foo')，removeAttribute('data-foo')，setAttribute('data-foo')，hasAttribute('data-foo')。
