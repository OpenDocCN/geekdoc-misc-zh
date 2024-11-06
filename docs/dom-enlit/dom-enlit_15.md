# 第十章 - DOM 中的 JavaScript

## 10.1 插入和执行 JavaScript 概述

JavaScript 可以通过包含外部 JavaScript 文件或编写页面级内联 JavaScript 的现代方式插入到 HTML 文档中，页面级内联 JavaScript 基本上是外部 JavaScript 文件的内容直接嵌入到 HTML 页面中作为文本节点。不要将包含在属性事件处理程序中的元素内联 JavaScript（即*<div onclick="alert('yo')"></div>*）与页面内联 JavaScript（即*<script>alert('hi')</script>*）混淆。

将 JavaScript 插入到 HTML 文档中的两种方法都需要使用*[<script>](http://www.whatwg.org/specs/web-apps/current-work/multipage/scripting-1.html#the-script-element)* [元素节点](http://www.whatwg.org/specs/web-apps/current-work/multipage/scripting-1.html#the-script-element)。*<script>*元素可以包含 JavaScript 代码，也可以用于使用*src*属性链接到外部 JavaScript 文件。下面的代码示例探讨了这两种方法。

实时代码：[`jsfiddle.net/domenlightenment/g6T5F`](http://jsfiddle.net/domenlightenment/g6T5F)

```
<!DOCTYPE html>
<html lang="en">
<body>

*<!-- external, cross domain JavaScript include* *-->*
<script src="http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"></script>

*<!-- page inline JavaScript* *-->*
<script>
console.log('hi');
</script>

</body>
</html>

```

### 注意事项

可以通过将 JavaScript 放置在元素属性事件处理程序中（即*<div onclick="alert('yo')"></div>*）和使用*javascript:*协议（例如*<a href="javascript:alert('yo')"></a>*）在 DOM 中插入和执行 JavaScript，但这不再被视为现代实践。

尝试在同一个*<script>*元素中包含外部 JavaScript 文件和编写页面内联 JavaScript 将导致页面内联 JavaScript 被忽略，而外部 JavaScript 文件被下载并执行。

自闭合脚本标签（即*<script src="" />*）应该避免，除非您正在使用一些老式的 XHTML。

*<script>*元素没有任何必需的属性，但提供以下可选属性：*async*、*charset*、*defer*、*src*和*type*。

页面内联 JavaScript 生成文本节点。这允许使用*innerHTML*和*textContent*来检索一行*<script>*的内容。然而，在浏览器解析 DOM 后将由 JavaScript 代码组成的新文本节点附加到 DOM 中，将不会执行新的 JavaScript 代码。它只是替换文本。

如果 JavaScript 代码包含字符串*'</script>'*，则必须使用*'<\/script>'*转义关闭*'/'*，以便解析器不认为这是真正的闭合*</script>*元素。

## 10.2 JavaScript 默认同步解析

默认情况下，当 DOM 被解析并遇到一个*<script>*元素时，它将停止解析文档，阻止进一步的渲染和下载，并执行 JavaScript。由于这种行为是阻塞的，不允许 DOM 的并行解析或 JavaScript 的执行，因此被认为是同步的。如果 JavaScript 是外部的 html 文档，阻塞会加剧，因为必须先下载 JavaScript 才能解析。在下面的代码示例中，我评论了浏览器在 DOM 中遇到几个*<script>*元素时发生的情况。

实时代码：[`jsfiddle.net/domenlightenment/rF3Lh`](http://jsfiddle.net/domenlightenment/rF3Lh)

```
<!DOCTYPE html>
<html lang="en">
<body>

**<!-- stop document parsing, block document parsing, load js, exectue js, then resume document parsing...* *-->* ***<script src="http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"></script>***<!-- stop document parsing, block document parsing, exectue js, then resume document parsing...* *-->***<script>console.log('hi');</script>** ****</body>
</html>****** 
```

*****您应该注意内联脚本和外部脚本在加载阶段的差异。

### 注释

*<script>*元素的默认阻塞特性对 HTML 网页的视觉渲染性能和感知性能有显著影响。如果在 html 页面的开头有几个脚本元素，除了下载和执行，没有其他事情发生（例如 DOM 解析和资源加载），直到每个脚本按顺序下载和执行。

## 10.3 推迟下载和执行外部 JavaScript 使用*defer*

*<script>*元素有一个名为*defer*的属性，它将延迟外部 JavaScript 文件的阻塞、下载和执行，直到浏览器解析了闭合的*<html>*节点。使用此属性简单地推迟了当 Web 浏览器遇到*<script>*节点时通常发生的事情。在下面的代码中，我将每个外部 JavaScript 文件推迟到最后遇到*<html>*。

实时代码：[`jsfiddle.net/domenlightenment/HDegp`](http://jsfiddle.net/domenlightenment/HDegp)

```
<!DOCTYPE html>
<html lang="en">
<body>

*<!-- defer, don't block just ignore this until the <html> element node is parsed -->*
<script defer src="http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"></script>*<!-- defer, don't block just ignore this until the <html> element node is parsed* *-->*
<script defer src="http://cdnjs.cloudflare.com/ajax/libs/jquery/1.7.2/jquery.min.js"></script>

*<!-- defer, don't block just ignore this until the <html> element node is parsed* *-->*
<script defer src="http://cdnjs.cloudflare.com/ajax/libs/jquery-mousewheel/3.0.6/jquery.mousewheel.min.js"></script>

<script>
*//We know that jQuery is not avaliable because this occurs before the closing <html> element*
console.log(window['jQuery'] === undefined); *//logs true*

*//Only after everything is loaded can we safley conclude that jQuery was loaded and parsed*
document.body.onload = function(){console.log(jQuery().jquery)}; *//logs function*
</script> 

</body>
</html>

```

### 注释

根据规范，延迟脚本应该按照文档顺序执行，并在*DOMContentLoaded*事件之前执行。然而，现代浏览器对此规范的遵守并不一致。

*defer*是一个布尔属性，它没有值。

一些浏览器支持延迟内联脚本，但这在现代浏览器中并不常见。

使用*defer*的假设是在延迟执行的 JavaScript 中不使用*document.write()*。

## 10.4 使用*async*异步下载和执行外部 JavaScript 文件

*<script>*元素有一个名为*async*的属性，当 Web 浏览器构建 DOM 时，它将覆盖*<script>*元素的顺序阻塞特性。通过使用此属性，我们告诉浏览器不要阻止构建（即 DOM 解析，包括下载其他资源如图像、样式表等...）html 页面，并放弃顺序加载。

通过使用*async*属性，文件会并行加载，并按照下载顺序解析一旦它们完全下载。在下面的代码中，我解释了在 Web 浏览器解析和渲染 HTML 文档时发生的情况。

实时代码：[`jsfiddle.net/domenlightenment/`](http://jsfiddle.net/domenlightenment/)

```
<!DOCTYPE html>
<html lang="en">
<body>

****<!-- Don't block, just start downloading and then parse the file when it's done downloading -->***
<script **async** src="http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"></script>**<!-- Don't block, just start downloading and then parse the file when it's done downloading -->* <script **async** src="http://cdnjs.cloudflare.com/ajax/libs/jquery/1.7.2/jquery.min.js"></script> *<!-- Don't block, just start downloading and then parse the file when it's done downloading -->* <script **async** src="http://cdnjs.cloudflare.com/ajax/libs/jquery-mousewheel/3.0.6/jquery.mousewheel.min.js"></script>
 *<script>
*// we have no idea if jQuery has been loaded yet likley not yet...*
console.log(window['jQuery'] === undefined);*//logs true*

*//Only after everything is loaded can we safley conclude that jQuery was loaded and parsed*
document.body.onload = function(){console.log(jQuery().jquery)}*;
</script> 

</body>
</html>**** 
```

***### 注意事项

IE 10 支持*async*，但 IE 9 不支持

使用*async*属性的一个主要缺点是 JavaScript 文件可能会按照它们在 DOM 中包含的顺序被解析。这会引发依赖管理问题。

*async*是一个布尔属性，它没有值

通过使用*async*，假设 JavaScript 中没有使用*document.write()*，那么将会被推迟的 JavaScript 不会出现问题

如果在*<script>*元素上同时使用*async*和*defer*，*async*属性将覆盖*defer*。

## 10.5 强制异步下载和解析外部 JavaScript 使用动态*<script>*

强制 Web 浏览器进行异步 JavaScript 下载和解析的已知方法，而不使用*async*属性，是通过编程方式创建包含外部 JavaScript 文件的*<script>*元素，并将其插入 DOM 中。在下面的代码中，我通过编程方式创建*<script>*元素节点，然后将其附加到*<body>*元素中，这迫使浏览器将*<script>*元素异步处理。

实时代码：[`jsfiddle.net/domenlightenment/du94d`](http://jsfiddle.net/domenlightenment/du94d)

```
<!DOCTYPE html>
<html lang="en">
<body>

*<!-- Don't block, just start downloading and then parse the file when it's done downloading -->*
<script>
var underscoreScript = document.createElement("script"); 
underscoreScript.src = "http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"; 
document.body.appendChild(underscoreScript);
</script>

*<!-- Don't block, just start downloading and then parse the file when it's done downloading -->*
<script>
var jqueryScript = document.createElement("script");
jqueryScript.src = "http://cdnjs.cloudflare.com/ajax/libs/jquery/1.7.2/jquery.min.js"; 
document.body.appendChild(jqueryScript);
</script>

*<!-- Don't block, just start downloading and then parse the file when it's done downloading -->*
<script>
var mouseWheelScript = document.createElement("script");
mouseWheelScript.src = "http://cdnjs.cloudflare.com/ajax/libs/jquery-mousewheel/3.0.6/jquery.mousewheel.min.js"; 
document.body.appendChild(mouseWheelScript);
</script>

<script>
*//Only after everything is loaded can we safley conclude that jQuery was loaded and parsed*
document.body.onload = function(){console.log(jQuery().jquery)}*;
</script>

</body>
</html>* 
```

*### 注意事项

使用动态*<script>*元素的一个主要缺点是 JavaScript 文件可能会按照它们在 DOM 中包含的顺序被解析。这会引发依赖管理问题。

## 10.6 使用异步*<script>*的*onload*回调，以便我们知道何时加载完成

*<script>*元素支持一个加载事件（即*onload*）处理程序，一旦外部 JavaScript 文件被加载和执行，它将执行。在下面的代码中，我利用*onload*事件来创建一个回调，程序化地通知我们 JavaScript 文件何时被下载和执行。

实时代码：[`jsfiddle.net/domenlightenment/XzAFx`](http://jsfiddle.net/domenlightenment/XzAFx)

```
<!DOCTYPE html>
<html lang="en">
<body>

*<!-- Don't block, just start downloading and then parse the file when it's done downloading -->*
<script>
var underscoreScript = document.createElement("script"); 
underscoreScript.src = "http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js";
underscoreScript.onload = function(){console.log('underscsore is loaded and exectuted');};
document.body.appendChild(underscoreScript);
</script>

*<!-- Don't block, just start downloading and then parse the file when it's done downloading -->*
<script async src="http://cdnjs.cloudflare.com/ajax/libs/jquery/1.7.2/jquery.min.js" onload="console.log('jQuery is loaded and exectuted');"></script>

</body>
</html>

```

### 注意事项

*onload*事件只是冰山一角[在支持*onload*的地方可用](http://pieisgood.org/test/script-link-events/)，你还可以使用*onerror*、*load*和*error*。

## 10.7 谨慎处理*<script>*在 HTML 中的位置以进行 DOM 操作

鉴于*<script>*元素的同步性质，如果将其放置在 HTML 文档的*<head>*元素中，会出现时间问题，如果 JavaScript 执行依赖于在*<script>*之前的任何 DOM，那么会出现 JavaScript 错误。简而言之，如果在操作 DOM 的 JavaScript 在其之前执行，你将会得到一个 JavaScript 错误。通过以下代码示例证明：

实时代码：N/A

```
<!DOCTYPE html>
<html lang="en">
<head>
*<!-- stop parsing, block parsing, exectue js then resume... -->*
<script>
*//we can't script the body element yet, its null, not even been parsed by the browser, its not in the DOM yet* 
console.log(document.body.innerHTML); *//logs Uncaught TypeError: Cannot read property 'innerHTML' of null* 
</script>
</head>
<body>
<strong>Hi</strong>
</body>
</html>

```

许多开发者，我自己也是其中之一，因此会尝试将所有*<script>*元素放置在闭合的*</body>*元素之前。通过这样做，你可以放心地确保*<script>*前面的 DOM 已经被解析并准备好进行脚本编写。此外，这种策略还将消除对 DOM 就绪事件的依赖，这可以使代码库更加清晰。

## 10.8 获取 DOM 中*<script>*元素的列表

从文档对象中提供的*document.scripts*属性提供了一个列表（即*HTMLCollection*），其中包含当前 DOM 中的所有脚本。在下面的代码中，我利用这个属性来访问每个*<script>*元素的*src*属性。

内联代码：N/A

```
<!DOCTYPE html>
<html lang="en">
<body>
<script src="http://cdnjs.cloudflare.com/ajax/libs/underscore.js/1.3.3/underscore-min.js"></script>
<script src="http://cdnjs.cloudflare.com/ajax/libs/jquery/1.7.2/jquery.min.js"></script>
<script src="http://cdnjs.cloudflare.com/ajax/libs/jquery-mousewheel/3.0.6/jquery.mousewheel.min.js"></script>

<script>​
Array.prototype.slice.call(document.scripts).forEach(function(elm){
	console.log(elm); 
});*//will log each script element in the document*
</script> 

</body>
</html>

```*********
