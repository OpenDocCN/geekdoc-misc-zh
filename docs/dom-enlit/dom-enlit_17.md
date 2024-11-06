# 第十二章 - 创建 dom.js - 一个受 jQuery 启发的现代浏览器 DOM 库

## 12.1 dom.js 概述

我希望你从这本书中获取信息和知识，并在我为你介绍一个名为 dom.js 的愿望、现代、类似 jQuery 的 DOM 库的基础时加以利用。将 dom.js 视为一个用于选择 DOM 节点并对其进行操作的现代库的基础。与 jQuery 类似，dom.js 代码将提供一个用于从 DOM 中选择（或创建）某些内容，然后对其进行操作的函数。我在下面展示了一些 *dom()* 函数的示例，如果你熟悉 jQuery 或任何用于选择元素的 DOM 工具，这些示例看起来应该不会陌生。

```
*//select in a document all li's in the first ul and get the innerHTML for the first li*
dom('li','ul').html();

*//create html structure using a document fragment and get the innerHTML of ul*
dom('<ul><li>hi</li></ul>').html()
```

对于大多数读者来说，本章节只是一个将本书中的信息应用到 JavaScript DOM 库的练习。对于其他人来说，这可能会让他们对 jQuery 本身以及当今 JavaScript 框架中使用的任何 DOM 操作逻辑有所了解。理想情况下，我希望这个练习能激发读者在适当时候根据需要打造自己的微型 DOM 抽象。说了这么多，让我们开始吧。

## 12.2 创建一个独特的作用域

为了保护我们的 dom.js 代码不受全局作用域的影响，我将首先创建一个独特的作用域，让它可以在其中生存和运行，而不必担心在全局作用域中发生冲突。在下面的代码中，我设置了一个相当标准的[立即调用函数表达式](http://benalman.com/news/2010/11/immediately-invoked-function-expression/)来创建这个私有作用域。当调用 IIFE 时，*global* 的值将设置为当前全局作用域（即 *window*）。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
(function(win){ 

var global = win;
var doc = this.document;

}}(window);
```

*在 IIFE 中，我们设置了对 *window* 和 *document* 对象（即 *doc*）的引用，以加快在 IIFE 中访问这些对象的速度。

## 12.3 创建 *dom()* 和 *GetOrMakeDom()* 函数，将 *dom()* 和 *GetOrMakeDom.prototype* 暴露给全局作用域

就像 jQuery 一样，我们将创建一个函数，该函数将根据传入的参数返回一个可链式调用的包装集合（即自定义类似数组的对象）的 DOM 节点（例如 *{0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}*）。在下面的代码中，我设置了 *dom()* 函数和传递给 *GetOrMakeDOM* 构造函数的参数，当调用时将返回包含 DOM 节点的对象，然后由 *dom()* 返回。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
(function(win){ 

var global = win;
var doc = global.document;

var dom = function(params,context){
	return new GetOrMakeDom(params,context);
};

var GetOrMakeDom = function(params,context){

}; *})(window);*
```

**为了使*dom()*函数能够从 IIFE 设置的私有范围外部访问/调用，我们必须将 dom 函数暴露（即创建引用）到全局范围。这是通过在全局范围中创建一个名为*dom*的属性并将该属性指向本地*dom()*函数来完成的。当从全局范围访问*dom*时，它将指向我本地作用域的*dom()*函数。在下面的代码中，*global.dom = dom;*就是这样做的技巧。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
(function(win){

var global = win;
var doc = global.document;
var dom = function(params,context){
	return new GetOrMakeDom(params,context);
};

var GetOrMakeDom = function(params,context){

};

*//expose dom to global scope*
global.dom = dom;

})(window);
```

我们需要做的最后一件事是将*GetOrMakeDom.prototype*属性暴露给全局范围。与 jQuery 类似（例如*jQuery.fn*），我们只需提供一个从*dom.fn*到*GetOrMakeDOM.prototype*的快捷引用。下面的代码显示了这一点。

```
(function(win){

var global = win;
var doc = global.document;
var dom = function(params,context){
	return new GetOrMakeDom(params,context);
};

var GetOrMakeDom = function(params,context){

};

*//expose dom to global scope*
global.dom = dom;

*//short cut to prototype*
dom.fn = GetOrMakeDom.prototype;

})(window);
```

*现在，任何附加到*dom.fn*的内容实际上都是*GetOrMakeDOM.prototype*对象的属性，并且在为从*GetOrMakeDOM*构造函数创建的任何对象实例进行属性查找时继承。

### 注意

使用*new*运算符调用*getOrMakeDom*函数。确保你[了解](https://developer.mozilla.org/zh-CN/docs/Web/JavaScript/Reference/Operators/new)当使用*new*运算符调用函数时会发生什么。

## 12.4 创建传递给*dom()*的可选上下文参数

当调用*dom()*时，它还会调用*GetOrMakeDom*函数，并将发送给*dom()*的参数传递给它。当调用*GetOrMakeDOM*构造函数时，我们需要做的第一件事是确定上下文。用于处理 DOM 的上下文可以通过传递用于选择节点的选择器字符串或节点引用本身来设置。如果不明显，将上下文传递给*dom()*函数的目的是提供将元素节点搜索限制到 DOM 树的特定分支的能力。这与传递给*jQuery*或*$*函数的第二个参数非常相似，几乎相同。在下面的代码中，我将上下文默认设置为全局范围中找到的当前文档。如果有上下文参数可用，我会确定它是什么（即字符串还是节点），然后要么使传递给上下文的节点，要么通过*querySelectorAll()*选择节点。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
(function(win){

var global = win;
var doc = global.document;
var dom = function(params,context){
	return new GetOrMakeDom(params,context);
};

var GetOrMakeDom = function(params,context){

 var currentContext = doc;
		if(context){
			if(context.nodeType){*//its either a document node or element node*
				currentContext = context;
			}else{ *//else its a string selector, use it to selector a node*
				currentContext = doc.querySelector(context);
		}
	}

};

*//expose dom to global scope*
global.dom = dom;

*//short cut to prototype*
dom.fn = GetOrMakeDom.prototype;

})(window);
```

通过设置*context*参数逻辑，我们可以接下来添加处理*params*参数所需的逻辑，以实际选择或创建节点。

## 12.5 根据*params*填充对象并返回 DOM 节点引用的对象

传递给*dom()*的*params*参数，然后传递给*getOrMakeDom()*，可以传递的参数类型不同。与 jQuery 类似，传递的值的类型可以是以下任何一种：

+   css 选择器字符串（例如*dom('body')*）

+   html 字符串（例如*dom('<p>你好</p><p> 世界！</p>')*）

+   *Element* 节点 (例如 *dom(document.body)*)

+   元素节点数组 (例如 *dom([document.body])*)

+   一个 *NodeList* (例如 *dom(document.body.children)*)

+   一个 *HTMLcollection* (例如 *dom(document.all)*)

+   一个 *dom()* 对象本身。 (例如 *dom(dom())*)

传递 *params* 的结果是构造一个包含节点引用的可链式对象 (例如 *{0:ELEMENT_NODE,1:ELEMENT_NODE,length:2})*，无论是在 DOM 中还是在文档片段中。 让我们看看如何使用上述每个参数来生成包含节点引用的对象。

允许如此多种参数类型的逻辑如下所示，并从简单检查 *params* 是否为 *undefined*、空字符串或带有空格的字符串开始。 如果是这种情况，我们向从调用 *GetOrMakeDOM* 构造的对象添加一个值为 *0* 的 *length* 属性，并返回该对象，以便函数的执行结束。 如果 *params* 不是假值 ([或类似假值](http://javascriptweblog.wordpress.com/2011/02/07/truth-equality-and-javascript/))，则函数的执行继续。

接下来是 *params* 值，如果是字符串，则检查是否包含 HTML。 如果字符串包含 HTML，则创建一个 [文档片段](https://developer.mozilla.org/en-US/docs/DOM/DocumentFragment)，并将字符串用作包含在文档片段中的 *<div>* 的 *innerHTML* 值，以便将字符串转换为 DOM 结构。 将 HTML 字符串转换为节点树后，循环访问顶级节点，并将对这些节点的引用传递给 *GetOrMakeDom* 创建的对象。 如果字符串不包含 HTML，则继续执行函数。

下一个检查简单地验证 *params* 是否是对单个节点的引用，如果是，则将其包装在对象中并返回，否则我们可以确定 *params* 的值是 [HTML 集合](https://developer.mozilla.org/en-US/docs/DOM/HTMLCollection)、[节点列表](https://developer.mozilla.org/en-US/docs/DOM/NodeList)、数组、字符串 [选择器](http://www.quirksmode.org/css/contents.html) 或从 *dom()* 创建的对象。 如果它是一个字符串选择器，则通过在 *currentContext* 上调用 *queryselectorAll()* 方法创建一个节点列表。 如果它不是字符串选择器，我们遍历 HTML 集合、节点列表、数组或对象，提取节点引用，并使用这些引用作为从调用 *GetOrMakeDom* 返回的对象中的值。

*GetOrMakeDom()* 函数内的所有逻辑可能有点压倒性，只需意识到构造函数的目的是构造一个包含节点引用的对象 (例如 *{0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}*) 并将此对象返回给 *dom()*。

github 代码: [`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
(function(win){

var global = win;
var doc = global.document;
var dom = function(params,context){
	return new GetOrMakeDom(params,context);
};

var regXContainsTag = /^\s*<(\w+|!)[^>]*>/;

var GetOrMakeDom = function(params,context){

	var currentContext = doc;
	if(context){
		if(context.nodeType){
			currentContext = context;
		}else{
			currentContext = doc.querySelector(context);
		}
	}

 *//if no params, return empty dom() object*
	if(!params || params === '' || typeof params === 'string' && params.trim() === ''){
		this.length = 0;
		return this;
	}

	*//if HTML string, construct domfragment, fill object, then return object*
	if(typeof params === 'string' && regXContainsTag.test(params)){//yup its forsure html string
		*//create div & docfrag, append div to docfrag, then set its div's innerHTML to the string, then get first child*
		var divElm = currentContext.createElement('div');
		divElm.className = 'hippo-doc-frag-wrapper';
		var docFrag = currentContext.createDocumentFragment();
		docFrag.appendChild(divElm);
		var queryDiv = docFrag.querySelector('div');
		queryDiv.innerHTML = params;
		var numberOfChildren = queryDiv.children.length;
		*//loop over nodelist and fill object, needs to be done because a string of html can be passed with siblings*
		for (var z = 0; z < numberOfChildren; z++) {
			this[z] = queryDiv.children[z];
		}
		*//give the object a length value*
		this.length = numberOfChildren;
	 *//return object*
		return this; *//return e.g. {0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}*
	}

	*//if a single node reference is passed, fill object, return object*
	if(typeof params === 'object' && params.nodeName){
		this.length = 1;
		this[0] = params;
		return this;
	}

	*//if its an object but not a node assume nodelist or array, else its a string selector, so create nodelist*
	var nodes;
	if(typeof params !== 'string'){*//nodelist or array*
		nodes = params;
	}else{*//ok string*
		nodes = currentContext.querySelectorAll(params.trim());
	}
	*//loop over array or nodelist created above and fill object*
	var nodeLength = nodes.length;
	for (var i = 0; i < nodeLength; i++) {
		this[i] = nodes[i];
	}
	*//give the object a length value*
	this.length = nodeLength;
	*//return  object*
	return this; *//return e.g. {0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}*

};

*//expose dom to global scope*
global.dom = dom;

*//short cut to prototype*
dom.fn = GetOrMakeDom.prototype;

})(window);
​​​​​​​​​​​​​​​​​​​​​​​​​​​​​​​​
```

## 12.6 创建 *each()* 方法并使其成为可链式调用的方法

当我们调用 *dom()* 时，我们可以通过原型继承访问任何附加到 *dom.fn* 的内容。 （例如 *dom().each()*）。与 jQuery 方法附加到 *dom.fn* 类似，操作 *GetOrMakeDom* 构造函数创建的对象。下面的代码设置了 *each()* 方法。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
dom.fn.each = function (callback) {
	var len = this.length; *//the specific instance create from getOrMakeDom() and returned by calling dom()*
	for(var i = 0; i < len; i++){
		*//invoke the callback function setting the value of this to element node and passing it parameters*
		callback.call(this[i], i, this[i]);
	}
};​​​​​​​​​​​​​​​​​​​​​​​​​​​​​​

```

正如你所预期的那样，*each()* 方法接受一个回调函数作为参数，并为 *getOrMakeDom* 对象实例中的每个节点元素调用该函数（使用 *call()* 将 *this* 值设置为元素节点对象）。*each()* 函数内部的 *this* 值是对 *getOrMakeDom* 对象实例的引用（例如 *{0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}*）。

当方法不返回值时（例如 *dom().length* 返回长度），允许方法链接是可能的，只需简单地返回方法所属的对象而不是特定的值。基本上，我们返回 *GetOrMakeDom* 对象，这样另一个方法就可以在该对象的实例上调用。在下面的代码中，我希望 *each()* 方法可以链接，意味着在调用 *each()* 后可以调用更多方法，所以我只需返回 *this*。下面代码中的 *this* 是从调用 *getOrMakeDom* 函数创建的对象实例。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
dom.fn.each = function (callback) {
	var len = this.length;
	for(var i = 0; i < len; i++){
		callback.call(this[i], i, this[i]);
	} return this; *//make it chainable by returning e.g. {0:ELEMENT_NODE,1:ELEMENT_NODE,length:2}**};​**​​**​​​​​​​​​​​​​​​​​​​​​​​​​​​* 
```

*## 12.7 创建 *html()*, *append()*, 和 *text()* 方法

有了核心*each()*方法的创建和隐式迭代的支持，我们现在可以构建一些*dom()*方法，以便操作我们从 HTML 文档中选择的节点，或者使用文档片段创建的节点。我们将要创建的三种方法是：

+   *html()* / *html('html string')*

+   *text()* / *text('text string')*

+   *append('html | text | dom() | nodelist/HTML collection | node | array')*

*html()* 和 *text()* 方法遵循非常相似的模式。如果方法带有参数值，我们会循环遍历（使用 *dom.fn.each()* 进行隐式迭代）*getOrMakeDom* 对象实例中的每个元素节点，设置 *innerHTML* 值或 *textContent* 值。如果未发送参数，我们简单地返回 *getOrMakeDom* 对象实例中第一个元素节点的 *innerHTML* 或 *textContent* 值。下面你将看到这个逻辑的代码化。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
dom.fn.html = function(htmlString){
	if(htmlString){
		return this.each(function(){ *//notice I return this so its chainable if called with param*
			this.innerHTML = htmlString;
		});
	}else{
		return this[0].innerHTML;
	}
};

dom.fn.text = function(textString){
	if(textString){
		return this.each(function(){ *//notice I return this so its chainable if called with param*
			this.textContent = textString;
		});
	}else{
		return this[0].textContent.trim();
	}
};
```

*append()* 方法利用 *insertAdjacentHTML* 将接受一个 html 字符串、文本字符串、*dom()* 对象、nodelist/HTML 集合、单个节点或节点数组，并将其追加到所选节点。

github 代码：[`github.com/codylindley/domjs/blob/master/builds/dom.js`](https://github.com/codylindley/domjs/blob/master/builds/dom.js)

```
dom.fn.append = function(stringOrObject){
	return this.each(function(){
		if(typeof stringOrObject === 'string'){
			this.insertAdjacentHTML('beforeend',stringOrObject);
		}else{
			var that = this;
			dom(stringOrObject).each(function(name,value){
				that.insertAdjacentHTML('beforeend',value.outerHTML);
			});
		}
	});
};
```

## 12.8 **运用 dom.js**

在创建[dom.js 我创建了一些非常简单的 qunit 测试](https://github.com/codylindley/domjs/tree/master/test)，我们现在将在测试框架之外运行这些测试。然而，你也可以[运行测试框架](https://github.com/codylindley/domjs/blob/master/test/index.html)来看 dom.js 的运行情况。以下代码演示了本章中创建的代码。

实时代码：[`jsfiddle.net/domenlightenment/7aqKm`](http://jsfiddle.net/domenlightenment/7aqKm)

```
<!DOCTYPE html>
<html lang="en">
<body>

<ul>
<li>1</li>
<li>2</li>
<li>3</li>
</ul>

<script src="https://raw.github.com/codylindley/domjs/master/builds/dom.js"></script>
<script>

*//dom()*
console.log(dom());
console.log(dom(''));
console.log(dom('body'));
console.log(dom('<p>Hellow</p><p> World!</p>'));
console.log(dom(document.body));
console.log(dom([document.body, document.body]));
console.log(dom(document.body.children));
console.log(dom(dom('body')));

*//dom().html()*
console.log(dom('ul li:first-child').html('one'));
console.log(dom('ul li:first-child').html() === 'one');

*//dom().text()*
console.log(dom('ul li:last-child').text('three'));
console.log(dom('ul li:last-child').text() === 'three');

*//dom().append()*
dom('ul').append('<li>4</li>');
dom('ul').append(document.createElement('li'));
dom('ul').append(dom('li:first-child'));

</script> 
</body>
</html>

```

## 12.9 总结 & 继续 dom.js

本章主要是关于创建类似于 jQuery 的 DOM 库的基础。如果你想继续学习构建类似于 jQuery 的 DOM 库的基础知识，我建议查看[hippo.js](https://github.com/codylindley/hippojs)，这是一个重新为现代浏览器创建 jQuery DOM 方法的练习。[dom.js](https://github.com/codylindley/domjs)和[hippo.js](https://github.com/codylindley/hippojs)都使用了[grunt](http://gruntjs.com/)、[QUnit](http://qunitjs.com/)和[JS Hint](http://jshint.com/)，如果你对构建自己的 JavaScript 库感兴趣，我强烈推荐你研究一下这些工具。除了上述开发工具，我还强烈建议阅读《[设计更好的 JavaScript API](http://coding.smashingmagazine.com/2012/10/09/designing-javascript-apis-usability/)》。现在去为 DOM 构建一些东西吧。
