# 第九章 - CSS 样式表和 CSS 规则

## 9.1 CSS 样式表概述

通过使用*HTMLLinkElement*节点（即*<link href="stylesheet.css" rel="stylesheet" type="text/css">*）包含外部样式表或使用*HTMLStyleElement*节点（即*<style></style>*）内联定义样式表，可以将样式表添加到 HTML 文档中。在下面的 HTML 文档中，这两个*Element*节点都在 DOM 中，我验证了哪个构造函数构造了这些节点。

实时代码：[`jsfiddle.net/domenlightenment/yPYyC`](http://jsfiddle.net/domenlightenment/yPYyC)

```
<!DOCTYPE html>
<html lang="en">
<head>

<link id="linkElement" href="http://yui.yahooapis.com/3.3.0/build/cssreset/reset-min.css" rel="stylesheet" type="text/css">

<style id="styleElement">
body{background-color:#fff;}
</style>

</head>
<body>

<script>

*//logs function HTMLLinkElement() { [native code] }*
console.log(document.querySelector('#linkElement').constructor);

*//logs function HTMLStyleElement() { [native code] }*
console.log(document.querySelector('#styleElement').constructor);

</script>
</body>
</html>

```

一旦将样式表添加到 HTML 文档中，它将由*CSSStylesheet*对象表示。样式表中的每个 CSS 规则（例如*body{background-color:red;}*）都由*CSSStyleRule*对象表示。在下面的代码中，我验证了哪个构造函数构造了样式表以及样式表中的每个 CSS 规则（选择器及其 CSS 属性和值）。

实时代码：[`jsfiddle.net/domenlightenment/UpLzm`](http://jsfiddle.net/domenlightenment/UpLzm)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
body{background-color:#fff;}
</style>

</head>
<body>

<script>

*//logs function CSSStyleSheet() { [native code] } because this object is the stylesheet itself*
console.log(document.querySelector('#styleElement').sheet.constructor);

*//logs function CSSStyleRule() { [native code] } because this object is the rule inside of the style sheet*
console.log(document.querySelector('#styleElement').sheet.cssRules[0].constructor); *</script>
</body>
</html>* 
```

*请记住，选择包含样式表的元素（即*<link>*或*<style*>)与访问代表样式表本身的实际对象（*CSSStyleSheet*）不同。

## 9.2 访问 DOM 中的所有样式表（即*CSSStylesheet*对象）

*document.styleSheets*提供对所有显式链接（即*<link>*）或嵌入（即*<style>*）在 HTML 文档中的所有样式表对象（也称为*CSSStylesheet*）的列表的访问。在下面的代码中，*styleSheets*被利用来访问文档中包含的所有样式表。

实时代码：N/A

```
<!DOCTYPE html>
<html lang="en">
<head>

<link href="http://yui.yahooapis.com/3.3.0/build/cssreset/reset-min.css" rel="stylesheet" type="text/css">

<style>
body{background-color:red;}
</style>

</head>
<body>

<script>

console.log(document.styleSheets.length); *//logs 2*
console.log(document.styleSheets[0]); *// the <link>*
console.log(document.styleSheets[1]); *// the <style>*

</script>
</body>
</html>

```

### 注意

*styleSheet*与其他节点列表一样是实时的

*length*属性返回列表中包含的样式表数量，从 0 索引开始（即*document.styleSheets.length*）

*styleSheets*列表中包含的样式表通常包括使用*<style>*元素创建的任何样式表，或者使用*<link>*元素并将*rel*设置为*"stylesheet"*的样式表。

除了使用*styleSheets*来访问文档样式表之外，还可以通过首先选择 DOM 中的元素（*<style>*或*<link>*）并使用*.sheet*属性来访问*CSSStyleSheet*对象来访问 HTML 文档中的样式表。在下面的代码中，我通过首先选择用于包含样式表的元素，然后利用*sheet*属性来访问 HTML 文档中的样式表。

实时代码：[`jsfiddle.net/domenlightenment/jFwKw`](http://jsfiddle.net/domenlightenment/jFwKw)

```
<!DOCTYPE html>
<html lang="en">
<head>

<link id="linkElement" href="http://yui.yahooapis.com/3.3.0/build/cssreset/reset-min.css" rel="stylesheet" type="text/css">

<style id="styleElement">
body{background-color:#fff;}
</style>

</head>
<body>

<script>

*//get CSSStylesheeet object for <link>*
console.log(document.querySelector('#linkElement').sheet); *//same as document.styleSheets[0]* **//get CSSSstylesheet object for <style>*
console.log(document.querySelector('#styleElement').**sheet**); *//same as document.styleSheets[1]*

</script>
</body>
</html>* 
```

***## 9.3 *CSSStyleSheet*属性和方法

要获取有关*CSSStyleSheet*节点上可用属性和方法的准确信息，最好忽略规范，并询问浏览器提供的内容。检查下面代码中创建的数组，详细说明了*CSSStyleSheet*节点可用的属性和方法。

在线代码：[`jsfiddle.net/domenlightenment/kNyL2`](http://jsfiddle.net/domenlightenment/kNyL2)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
body{background-color:#fff;}
</style>

</head>
<body>

<script>

var styleSheet = document.querySelector('#styleElement').sheet;

*//text own properties*
console.log(Object.keys(styleSheet).sort());

*//text own properties & inherited properties*
var styleSheetPropertiesIncludeInherited = [];
for(var p in styleSheet){
	styleSheetPropertiesIncludeInherited.push(p);
}
console.log(styleSheetPropertiesIncludeInherited.sort());

*//text inherited properties only*
var styleSheetPropertiesOnlyInherited = [];
for(var p in styleSheet){
	if(!styleSheet.hasOwnProperty(p)){
		styleSheetPropertiesOnlyInherited.push(p);
	}
}
console.log(styleSheetPropertiesOnlyInherited.sort());

</script>
</body>
</html>

```

从 *styleSheets* 列表或通过 *.sheet* 属性访问的 *CSSStyleSheet* 对象具有以下属性和方法：

+   *disabled*

+   *href*

+   *media*

+   *ownerNode*

+   *parentStylesheet*

+   *title*

+   *type*

+   *cssRules*

+   *ownerRule*

+   *deleteRule*

+   *inserRule*

### 注释

*href*、*media*、*ownerNode*、*parentStylesheet*、*title* 和 *type* 是只读属性，不能使用这些属性设置其值。

## 9.4 *CSSStyleRule* 概述

*CSSStyleRule* 对象代表样式表中包含的每个 CSS 规则。基本上，*CSSStyleRule* 是与选择器附加的 CSS 属性和值的接口。在下面的代码中，我们通过访问代表样式表中 CSS 规则的 *CSSStyleRule* 对象，以编程方式访问内联样式表中每个规则的详细信息。

在线代码：[`jsfiddle.net/domenlightenment/fPVS8`](http://jsfiddle.net/domenlightenment/fPVS8)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
body{background-color:#fff;margin:20px;} */*this is a css rule*/*
p{line-height:1.4em; color:blue;} */*this is a css rule*/*
</style>

</head>
<body>

<script>

var sSheet = document.querySelector('#styleElement');

console.log(sSheet.cssRules[0].cssText); *//logs "body { background-color: red; margin: 20px; }"*
console.log(sSheet.cssRules[1].cssText); *//logs "p { line-height: 1.4em; color: blue; }"*

</script>
</body>
</html>

```

## 9.5 *CSSStyleRule* 属性和方法

要获取有关 *CSSStyleRule* 节点上可用属性和方法的准确信息，最好忽略规范，并询问浏览器提供的内容。检查下面代码中创建的数组，详细说明了从 *CSSStyleRule* 节点可用的属性和方法。

在线代码：[`jsfiddle.net/domenlightenment/hCX3U`](http://jsfiddle.net/domenlightenment/hCX3U)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
body{background-color:#fff;}
</style>

</head>
<body>

<script>

var styleSheetRule = document.querySelector('#styleElement').sheet.cssRule;

*//text own properties*
console.log(Object.keys(styleSheetRule).sort());

*//text own properties & inherited properties*
var styleSheetPropertiesIncludeInherited = [];
for(var p in styleSheetRule){
	styleSheetRulePropertiesIncludeInherited.push(p);
}
console.log(styleSheetRulePropertiesIncludeInherited.sort());

*//text inherited properties only*
var styleSheetRulePropertiesOnlyInherited = [];
for(var p in styleSheetRule){
	if(!styleSheetRule.hasOwnProperty(p)){
		styleSheetRulePropertiesOnlyInherited.push(p);
	}
}
console.log(styleSheetRulePropertiesOnlyInherited.sort());

</script>
</body>
</html>

```

通过 *CSSrule* 对象，可以对样式表中包含的规则（例如 *body{background-color:red;}*）进行脚本化处理。该对象提供以下属性：

+   *cssText*

+   *parentRule*

+   *parentStylesSheet*

+   *selectorText*

+   *style*

+   *type*

## 9.6 使用 *CSSRules* 获取样式表中的 CSS 规则列表

如前所述，*styleSheets* 列表提供了文档中包含的样式表列表。*CSSRules* 列表提供了特定样式表中所有 CSS 规则（即 *CSSStyleRule* 对象）的列表（也称为 *CSSRulesList*）。下面的代码将 *CSSRules* 列表记录到控制台中。

在线代码：[`jsfiddle.net/domenlightenment/qKqhJ`](http://jsfiddle.net/domenlightenment/qKqhJ)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
body{background-color:#fff;margin:20px;}
p{line-height:1.4em; color:blue;}
</style>

</head>
<body>

<script>

var sSheet = document.querySelector('#styleElement').sheet;

*//array like list containing all of the CSSrule objects repreesenting each CSS rule in the style sheet*
console.log(sSheet.cssRules);

console.log(sSheet.cssRules.length); *//logs 2*

*//rules are index in a CSSRules list starting at a 0 index*
console.log(sSheet.cssRules[0]); *//logs first rule*
console.log(sSheet.cssRules[1]); *//logs second rule*

</script>
</body>
</html>

```

## 9.7 使用 *.insertRule()* 和 *.deleteRule()* 在样式表中插入和删除 CSS 规则

*insertRule()* 和 *deleteRule()* 方法提供了以编程方式操作样式表中的 CSS 规则的能力。在下面的代码中，我使用 *insertRule()* 将 css 规则 *p{color:red}* 添加到索引为 1 的内联样式表中。请记住，样式表中的 css 规则是从 0 开始的数字索引。因此，通过在索引 1 处插入新规则，当前索引 1 处的规则（即 *p{font-size:50px;}*）被推到索引 2。

在线代码：[`jsfiddle.net/domenlightenment/T2jzJ`](http://jsfiddle.net/domenlightenment/T2jzJ)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
p{line-height:1.4em; color:blue;} */*index 0*/*
p{font-size:50px;} */*index 1*/*
</style>

</head>
<body>

<p>Hi</p>

<script>

*//add a new CSS rule at index 1 in the inline style sheet*
document.querySelector('#styleElement').sheet.insertRule('p{color:red}',1);

*//verify it was added*
console.log(document.querySelector('#styleElement').sheet.cssRules[1].cssText);

*//Delete what we just added* document.querySelector('#styleElement').sheet.deleteRule(1);

*//verify it was removed*
console.log(document.querySelector('#styleElement').sheet.cssRules[1].cssText);

</script>
</body>
</html>

```

删除规则就像在样式表上调用 *deleteRule()* 方法并传递要删除的规则在样式表中的索引一样简单。

### 注释

插入和删除规则不是一个常见的做法，因为在管理级联和使用数字索引系统更新样式表时存在困难（即确定样式位于哪个索引位置，而不预览样式表本身的内容）。在将 CSS 规则在客户端程序化地更改之前，最好在 CSS 和 HTML 文件中处理它们，而不是在客户端之后。

## 9.8 使用*.style*属性编辑*CSSStyleRule*的值

就像*.style*属性有助于操纵元素节点上的内联样式一样，*CSSStyleRule*对象也有一个*.style*属性，用于在样式表中编排相同的样式操纵。在下面的代码中，我利用*.style*属性来设置和获取内联样式表中包含的 css 规则的值。

在线代码：[`jsfiddle.net/domenlightenment/aZ9CQ`](http://jsfiddle.net/domenlightenment/aZ9CQ)

```
<!DOCTYPE html>
<html lang="en">
<head>

<style id="styleElement">
p{color:blue;}
strong{color:green;}
</style>

</head>
<body>

<p>Hey <strong>Dude!</strong></p>

<script>

var styleSheet = document.querySelector('#styleElement').sheet;

*//Set css rules in stylesheet*
styleSheet.cssRules[0].style.color = 'red';
styleSheet.cssRules[1].style.color = 'purple';

*//Get css rules*
console.log(styleSheet.cssRules[0].style.color); *//logs 'red'*
console.log(styleSheet.cssRules[1].style.color); *//logs 'purple'*

</script>
</body>
</html>

```

## 9.9 创建新的内联 CSS 样式表

在加载 html 页面后动态创建新样式表只需创建一个新的*<style>*节点，使用*innerHTML*向该节点添加 CSS 规则，然后将*<style>*节点附加到 HTML 文档中。在下面的代码中，我程序化地创建一个样式表，并将*body{color:red}* CSS 规则添加到样式表中，然后将样式表附加到 DOM 中。

在线代码：[`jsfiddle.net/domenlightenment/bKXAk`](http://jsfiddle.net/domenlightenment/bKXAk)

```
<!DOCTYPE html>
<html lang="en">
<head></head>
<body>

<p>Hey <strong>Dude!</strong></p>

<script>

var styleElm = document.createElement('style');
styleElm.innerHTML = 'body{color:red}';

*//notice markup in the document changed to red from our new inline stylesheet*
document.querySelector('head').appendChild(styleElm);

</script>
</body>
</html>

```

## 9.10 在 HTML 文档中程序化地添加外部样式表

要在 HTML 文档中程序化地添加 CSS 文件，需要创建一个带有适当属性的*<link>*元素节点，然后将*<link>*元素节点附加到 DOM 中。在下面的代码中，我通过创建一个新的*<link>*元素并将其附加到 DOM 中来程序化地包含外部样式表。

在线代码：[`jsfiddle.net/domenlightenment/dtwgC`](http://jsfiddle.net/domenlightenment/dtwgC)

```
<!DOCTYPE html>
<html lang="en">
<head></head>
<body>

<script>

*//create & add attributes to <link>*
var linkElm = document.createElement('link');
linkElm.setAttribute('rel', 'stylesheet');
linkElm.setAttribute('type', 'text/css');
linkElm.setAttribute('id', 'linkElement');
linkElm.setAttribute('href', 'http://yui.yahooapis.com/3.3.0/build/cssreset/reset-min.css');

*//Append to the DOM*
document.head.appendChild(linkElm);

*//confrim its addition to the DOM*
console.log(document.querySelector('#linkElement'));

</script>
</body>
</html>

```

## 9.11 使用*disabled*属性禁用/启用样式表

使用*CSSStyleSheet*对象的*.disabled*属性，可以启用或禁用样式表。在下面的代码中，我们访问文档中每个样式表的当前禁用值，然后利用*.disabled*属性禁用每个样式表。

在线代码：[`jsfiddle.net/domenlightenment/L952Z`](http://jsfiddle.net/domenlightenment/L952Z)

```
<!DOCTYPE html>
<html lang="en">
<head>

<link id="linkElement" href="http://yui.yahooapis.com/3.3.0/build/cssreset/reset-min.css" rel="stylesheet" type="text/css">

<style id="styleElement">
body{color:red;}
</style>

</head>
<body>

<script>

*//Get current boolean disabled value*
console.log(document.querySelector('#linkElement').disabled); *//log 'false'*
console.log(document.querySelector('#styleElement').disabled); *//log 'false'*

*//Set disabled value, which of courese disabled all styles for this document*
document.document.querySelector('#linkElement').disabled = true;
document.document.querySelector('#styleElement').disabled = true;

</script>
</body>
</html>

```

### 注释

根据规范，*Disabled*不是<link>或<style>元素的可用属性。尝试将其作为 HTML 文档中的属性添加将在今天使用的大多数现代浏览器中失败（并且可能导致解析错误，其中样式被忽略）。
