# 第六章 - 元素节点内联样式

## 6.1 样式属性（又名元素内联 CSS 属性）概述

每个 HTML 元素都有一个样式属性，可以用于内联 CSS 属性特定于该元素。在下面的代码中，我正在访问包含多个内联 CSS 属性的*<div>*的*style*属性。

实时代码：[`jsfiddle.net/domenlightenment/A4Aph`](http://jsfiddle.net/domenlightenment/A4Aph)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div style="background-color:red;border:1px solid black;height:100px;width:100px;"></div>

<script>

var divStyle = document.querySelector('div').style; 

*//logs CSSStyleDeclaration {0="background-color", ...}*
console.log(divStyle);

 </script>
</body>
</html>
```

请注意上面代码中从*style*属性返回的是一个*CSSStyleDeclaration*对象，而不是一个字符串。此外，请注意*CSSStyleDeclaration*对象仅包括元素的内联样式（即不包括计算样式，计算样式是从样式表级联的任何样式）。

## 6.2 获取、设置和移除单个内联 CSS 属性

内联 CSS 样式被单独表示为元素节点对象的属性（即对象属性）的*style*对象。这为我们提供了通过简单设置对象属性值来获取、设置或移除元素上的单个 CSS 属性的接口。在下面的代码中，我们通过操纵*style*对象的属性来设置、获取和移除*<div>*上的样式。

实时代码：[`jsfiddle.net/domenlightenment/xNT85`](http://jsfiddle.net/domenlightenment/xNT85)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div></div>

<script>

var divStyle = document.querySelector('div').style;

*//set*
divStyle.backgroundColor = 'red';
divStyle.border = '1px solid black';
divStyle.width = '100px';
divStyle.height = '100px';

*//get*
console.log(divStyle.backgroundColor);
console.log(divStyle.border);
console.log(divStyle.width);
console.log(divStyle.height);

*/*remove
divStyle.backgroundColor = '';
divStyle.border = '';
divStyle.width = '';
divStyle.height = '';
*/*

</script>
</body>
</html>
```

### 注意

样式对象中的属性名不包含 CSS 属性名中使用的普通连字符。翻译相当简单。删除连字符并使用驼峰命名法（例如，font-size = *fontSize* 或 background-image = *backgroundImage*）。在 CSS 属性名是 JavaScript 关键字的情况下，JavaScript CSS 属性名前缀为"css"（例如，float = *cssFloat*）。

简写属性也可以作为属性使用。因此，你不仅可以设置*margin*，还可以设置*marginTop*。

请记住，对于需要单位的 css 属性值，请包含相应的单位（例如，*style.width = '300px';* 而不是 *style.width = '300';*）。在标准模式下呈现文档时，单位是必需的，否则将被忽略。在怪异模式下，如果没有包含单位，则会做出假设。

| CSS 属性 | JavaScript 属性 |
| --- | --- |
| background | background |
| background-attachment | backgroundAttachment |
| background-color | backgroundColor |
| background-image | backgroundImage |
| background-position | backgroundPosition |
| background-repeat | backgroundRepeat |
| border | border |
| border-bottom | borderBottom |
| border-bottom-color | borderBottomColor |
| border-bottom-style | borderBottomStyle |
| border-bottom-width | borderBottomWidth |
| border-color | borderColor |
| border-left | borderLeft |
| border-left-color | borderLeftColor |
| border-left-style | borderLeftStyle |
| border-left-width | borderLeftWidth |
| border-right | borderRight |
| border-right-color | borderRightColor |
| border-right-style | borderRightStyle |
| border-right-width | borderRightWidth |
| border-style | borderStyle |
| border-top | borderTop |
| border-top-color | borderTopColor |
| border-top-style | borderTopStyle |
| border-top-width | borderTopWidth |
| border-width | borderWidth |
| clear | clear |
| clip | clip |
| color | color |
| cursor | cursor |
| display | display |
| filter | filter |
| font | font |
| font-family | fontFamily |
| font-size | fontSize |
| font-variant | fontVariant |
| font-weight | fontWeight |
| height | height |
| left | left |
| letter-spacing | letterSpacing |
| line-height | lineHeight |
| list-style | listStyle |
| list-style-image | listStyleImage |
| list-style-position | listStylePosition |
| list-style-type | listStyleType |
| margin | margin |
| margin-bottom | marginBottom |
| margin-left | marginLeft |
| margin-right | marginRight |
| margin-top | marginTop |
| overflow | overflow |
| padding | padding |
| padding-bottom | paddingBottom |
| padding-left | paddingLeft |
| padding-right | paddingRight |
| padding-top | paddingTop |
| page-break-after | pageBreakAfter |
| page-break-before | pageBreakBefore |
| position | position |
| float | styleFloat |
| text-align | textAlign |
| text-decoration | textDecoration |
| text-decoration: blink | textDecorationBlink |
| text-decoration: line-through | textDecorationLineThrough |
| text-decoration: none | textDecorationNone |
| text-decoration: overline | textDecorationOverline |
| text-decoration: underline | textDecorationUnderline |
| text-indent | textIndent |
| text-transform | textTransform |
| top | top |
| vertical-align | verticalAlign |
| visibility | visibility |
| width | width |
| z-index | zIndex |

样式对象是一个*CSSStyleDeclaration*对象，它不仅提供对单个 CSS 属性的访问，还提供了用于在元素节点上操作单个 CSS 属性的*setPropertyValue(propertyName)*，*getPropertyValue(propertyName,value)*和*removeProperty()*方法。在下面的代码中，我们使用这些方法在*<div>*上设置、获取和移除单个 CSS 属性。

实时代码：[`jsfiddle.net/domenlightenment/X2DyX`](http://jsfiddle.net/domenlightenment/X2DyX)

```
<!DOCTYPE html>
<html lang="en">
<head>
<style>
</style>
</head>

<body>

<div style="background-color:green;border:1px solid purple;"></div>

<script>

var divStyle = document.querySelector('div').style;

*//set*
divStyle.**setProperty**('background-color','red');
divStyle.**setProperty**('border','1px solid black');
divStyle.**setProperty**('width','100px');
divStyle.**setProperty**('height','100px');

*//get*
console.log(divStyle.**getPropertyValue**('background-color'));
console.log(divStyle.**getPropertyValue**('border','1px solid black'));
console.log(divStyle.**getPropertyValue**('width','100px'));
console.log(divStyle.**getPropertyValue**('height','100px'));

*/*remove
divStyle.removeProperty('background-color');
divStyle.removeProperty('border');
divStyle.removeProperty('width');
divStyle.removeProperty('height');
*/*

</script>
</body>
</html>
```

### 注释

请注意，属性名称通过包含连字符的 css 属性名称（例如*background-color*而不是*backgroundColor*）传递给*setProperty()*和*getPropertyValue()*方法。

要了解更详细关于*setProperty()*，*getPropertyValue()*和*removeProperty()*以及其他属性和方法的信息，请查看由 Mozilla 提供的[文档](https://developer.mozilla.org/en/DOM/CSSStyleDeclaration)。

## 6.3 获取、设置和移除所有内联 CSS 属性

可以使用*CSSStyleDeclaration*对象的*cssText*属性以及*getAttribute()*和*setAttribute()*方法，通过 JavaScript 字符串获取、设置和移除整个（即所有内联 CSS 属性）style 属性的值。在下面的代码中，我们获取、设置和移除*<div>*上的所有内联 CSS（而不是单独更改 CSS 属性）。

实时代码：[`jsfiddle.net/domenlightenment/wSv8M`](http://jsfiddle.net/domenlightenment/wSv8M)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div></div>

<script>

var div = document.querySelector('div');
var divStyle = div.style;

*//set using cssText*
divStyle.cssText = 'background-color:red;border:1px solid black;height:100px;width:100px;';
*//get using cssText*
console.log(divStyle.cssText);
*//remove*
divStyle.cssText = '';

*//exactly that same outcome using setAttribute() and getAttribute()*

*//set using setAttribute*
div.setAttribute('style','background-color:red;border:1px solid black;height:100px;width:100px;');
*//get using getAttribute*
console.log(div.getAttribute('style'));
*//remove*
div.removeAttribute('style');

</script>
</body>
</html>
```

### 注意

如果不明显，您应该注意，用新字符串替换*style*属性值是对元素样式进行多次更改的最快方法。

## 6.4 使用*getComputedStyle()*获取元素的计算样式（即包括来自级联的任何实际样式）

*style*属性仅包含通过 style 属性定义的 CSS。要从级联中获取元素的 CSS（即从内联样式表、外部样式表、浏览器样式表级联）以及其内联样式，可以使用*getComputedStyle()*。该方法提供一个类似于*style*的只读*CSSStyleDeclaration*对象。在下面的代码示例中，我演示了读取级联样式，而不仅仅是元素内联样式。

实时代码：[`jsfiddle.net/domenlightenment/k3G5Q`](http://jsfiddle.net/domenlightenment/k3G5Q)

```
<!DOCTYPE html>
<html lang="en">
<head>
<style>
​div{
    background-color:red;
    border:1px solid black;
    height:100px;
    width:100px;
}
</style>
</head>

<body>

<div style="background-color:green;border:1px solid purple;"></div>

<script>

var div = document.querySelector('div');

*//logs rgb(0, 128, 0) or green, this is an inline element style*
console.log(window.getComputedStyle(div).backgroundColor);

*//logs 1px solid rgb(128, 0, 128) or 1px solid purple, this is an inline element style*
console.log(window.getComputedStyle(div).border);

*//logs 100px, note this is not an inline element style*
console.log(window.getComputedStyle(div).height);

*//logs 100px, note this is not an inline element style*
console.log(window.getComputedStyle(div).width);

</script>
</body>
</html>
```

请确保您注意*getComputedStyle()*方法遵守[CSS 特异性层次结构](http://css-tricks.com/specifics-on-css-specificity/)。例如，在刚刚显示的代码中，*<div>*的*backgroundColor*被报告为绿色而不是红色，因为内联样式位于特异性层次结构的顶部，因此浏览器应用的是内联*backgroundColor*值，并考虑其最终计算样式。

### 注意

从*getComputedStyles()*返回的*CSSStyleDeclaration*对象上不能设置任何值，它是只读的。

*getComputedStyles()*方法以*rgb(#,#,#)*格式返回颜色值，无论它们最初是如何编写的。

[简写](http://www.w3.org/TR/CSS21/about.html#shorthand)属性不会计算为*CSSStyleDeclaration*对象，您必须使用非简写属性名称来访问属性（例如 marginTop 而不是 margin）。

## 6.5 应用和移除元素上的 CSS 属性使用*class*和*id*属性

在内联样式表或外部样式表中定义的样式规则可以使用*class*和*id*属性添加或从元素中移除。这是操作元素样式的最常见模式。在下面的代码中，利用*setAttribute()*和*classList.add()*，通过设置*class*和*id*属性值，将内联样式规则应用于*<div>*。使用*removeAttribute()*和*classList.remove()*也可以移除这些 CSS 规则。

实时代码：[`jsfiddle.net/domenlightenment/BF9gM`](http://jsfiddle.net/domenlightenment/BF9gM)

```
<!DOCTYPE html>
<html lang="en">
<head>
<style>
.foo{
  background-color:red;
  padding:10px;
}
#bar{
  border:10px solid #000;
  margin:10px;
}
</style>
</head>
<body>

<div></div>

<script>

var div = document.querySelector('div');

*//set*
div.setAttribute('id','bar');
div.classList.add('foo');

*/*remove
div.removeAttribute('id');
div.classList.remove('foo');
*/*

</script>
</body>
</html>
```
