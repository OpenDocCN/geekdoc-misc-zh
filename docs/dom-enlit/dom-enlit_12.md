# 第七章 - 文本节点

## 7.1 *Text* 对象概述

HTML 文档中的文本由 *Text()* 构造函数的实例表示，该函数生成文本节点。当解析 HTML 文档时，混在 HTML 页面元素中的文本会被转换为文本节点。

实时代码：[`jsfiddle.net/domenlightenment/kuz5Z`](http://jsfiddle.net/domenlightenment/kuz5Z)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p>hi</p>

<script>
 *//select 'hi' text node*
var textHi = document.querySelector('p').firstChild

console.log(textHi.constructor); *//logs Text()*

*//logs Text {textContent="hi", length=2, wholeText="hi", ...}*
console.log(textHi);

</script>
</body>
</html>

```

上面的代码得出结论，*Text()* 构造函数构造了文本节点，但请记住，*Text* 继承自 *CharacterData*、*Node* 和 *Object*。

## 7.2 *Text* 对象和属性

要获取关于 *Text* 节点上可用属性和方法的准确信息，最好忽略规范，并询问浏览器提供了什么。查看下面代码中创建的数组，详细说明了文本节点可用的属性和方法。

实时代码：[`jsfiddle.net/domenlightenment/Wj3uS`](http://jsfiddle.net/domenlightenment/Wj3uS)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p>hi</p>

<script>
var text = document.querySelector('p').firstChild;

*//text own properties*
console.log(Object.keys(text).sort());

*//text own properties & inherited properties*
var textPropertiesIncludeInherited = [];
for(var p in text){
	textPropertiesIncludeInherited.push(p);
}
console.log(textPropertiesIncludeInherited.sort());

*//text inherited properties only*
var textPropertiesOnlyInherited = [];
for(var p in text){
	if(!text.hasOwnProperty(p)){
		textPropertiesOnlyInherited.push(p);
	}
}
console.log(textPropertiesOnlyInherited.sort());

</script>
</body>
</html>

```

即使未考虑继承的属性，可用属性仍然很多。下面我精选了一些值得注意的属性和方法列表，适用于本章的上下文。

+   *textContent*

+   *splitText()*

+   *appendData()*

+   *deleteData()*

+   *insertData()*

+   *replaceData()*

+   *subStringData()*

+   *normalize()*

+   *data*

+   *document.createTextNode()*（不是文本节点的属性或继承属性，但在本章讨论）

## 7.3 空格创建 *Text* 节点

当浏览器或通过编程方式构建 DOM 时，文本节点会从空格和文本字符中创建。毕竟，空格也是一个字符。在下面的代码中，第二段落包含一个空格，有一个子 *Text* 节点，而第一个段落没有。

实时代码：[`jsfiddle.net/domenlightenment/YbtnZ`](http://jsfiddle.net/domenlightenment/YbtnZ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p id="p1"></p>
<p id="p2"> </p>

<script>

console.log(document.querySelector('#p1').firstChild) *//logs null*
console.log(document.querySelector('#p2').firstChild.nodeName) *//logs #text*

</script>
</body>
</html>

```

不要忘记，DOM 中的空格和文本字符通常由文本节点表示。这当然意味着换行符被视为文本节点。在下面的代码中，我们记录了一个换行符，突出显示这种类型的字符实际上是一个文本节点。

实时代码：[`jsfiddle.net/domenlightenment/9FEzq`](http://jsfiddle.net/domenlightenment/9FEzq)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p id="p1"></p> *//yes there is a carriage return text node before this comment, even this comment is a node*
<p id="p2"></p>

<script>

console.log(document.querySelector('#p1').nextSibling) *//logs Text* *</script>
</body>
</html>* 
```

*事实上，如果您可以使用键盘将字符或空格输入到 HTML 文档中，那么它可能被解释为文本节点。如果您仔细考虑，除非最小化/压缩 HTML 文档，否则平均的 HTML 页面包含大量空格和换行符文本节点。

## 7.4 创建和注入 *Text* 节点

当浏览器解释 HTML 文档并基于文档内容构建相应的 DOM 时，*Text* 节点会自动为我们创建。事实上，还可以使用 *createTextNode()* 以编程方式创建 *Text* 节点。在下面的代码中，我创建一个文本节点，然后将该节点注入到实时 DOM 树中。

实时代码：[`jsfiddle.net/domenlightenment/xC9q3`](http://jsfiddle.net/domenlightenment/xC9q3)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div></div>

<script>

var textNode = document.createTextNode('Hi');
document.querySelector('div').appendChild(textNode);

console.log(document.querySelector('div').innerText); *// logs Hi*

</script>
</body>
</html>

```

请记住，我们也可以将文本节点注入到以编程方式创建的 DOM 结构中。在下面的代码中，我在将其注入到活动 DOM 之前，将一个文本节点放入了一个*<p>*元素中。

实时代码：[`jsfiddle.net/domenlightenment/PdatJ`](http://jsfiddle.net/domenlightenment/PdatJ)

```
<!DOCTYPE html>
<html lang="en">

<div></div>

<body>

<script>

var elementNode = document.createElement('p');
var textNode = document.createTextNode('Hi');
elementNode.appendChild(textNode);
document.querySelector('div').appendChild(elementNode);

console.log(document.querySelector('div').innerHTML); *//logs <div>Hi</div>*

</script>
</body>
</html>

```

## 7.5 使用*.data*或*nodeValue*获取*Text*节点值

通过使用*.data*或*nodeValue*属性，可以从*Text*节点中提取文本值/数据。这两者都返回*Text*节点中包含的文本。下面我展示了如何使用这两者来提取*<div>*中包含的值。

实时代码：[`jsfiddle.net/domenlightenment/dPLkx`](http://jsfiddle.net/domenlightenment/dPLkx)

```
<!DOCTYPE html>
<html lang="en">

<p>Hi, <strong>cody</strong></p><body>

<script>

console.log(document.querySelector('p').firstChild.data); *//logs 'Hi,'*
console.log(document.querySelector('p').firstChild.nodeValue); *//logs 'Hi,*'

</script>
</body>
</html>

```

注意，*<p>*包含两个*Text*节点和一个*Element*（即*<strong>*）节点。我们只获取包含在*<p>*中的第一个子节点的值。

### 注意

获取文本节点中包含的字符的长度就像访问节点本身的长度属性或节点的实际文本值/数据一样简单（即*document.querySelector('p').firstChild.length*或*document.querySelector('p').firstChild.data.length*或*document.querySelector('p').firstChild.nodeValue.length*）

## 7.6 使用*appendData()*，*deleteData()*，*insertData()*，*replaceData()*，*subStringData()*操纵*Text*节点

*CharacterData*对象从中继承方法的*Text*节点为操作和从*Text*节点值中提取子值提供了以下方法。

+   *appendData()*

+   *deleteData()*

+   *insertData()*

+   *replaceData()*

+   *subStringData()*

在下面的代码示例中，每一个都在代码中被利用。

实时代码：[`jsfiddle.net/domenlightenment/B6AC6`](http://jsfiddle.net/domenlightenment/B6AC6)

```
<!DOCTYPE html>
<html lang="en">

<p>Go big Blue Blue<body>

<script>

var pElementText = document.querySelector('p').firstChild;

*//add !*
pElementText.appendData('!');
console.log(pElementText.data);

*//remove first 'Blue'*
pElementText.deleteData(7,5);
console.log(pElementText.data);

*//insert it back 'Blue'*
pElementText.insertData(7,'Blue ');
console.log(pElementText.data);

*//replace first 'Blue' with 'Bunny'*
pElementText.replaceData(7,5,'Bunny ');
console.log(pElementText.data);

*//extract substring 'Blue Bunny'*
console.log(pElementText.substringData(7,10));

</script>
</body>
</html>

```

### 注意

相同的操作和子提取方法也可以被*Comment*节点所利用。

## 7.7 当存在多个兄弟*Text*节点时

通常，相邻的兄弟*Text*节点不会出现，因为浏览器创建的 DOM 树会智能地合并文本节点，然而存在两种情况使得相邻的文本节点可能。第一种情况相当明显。如果一个文本节点包含一个*Element*节点（例如*<p>嗨，<strong>cody</strong>欢迎！</p>*），那么文本将被拆分成正确的节点组。最好查看一个代码示例，因为这可能听起来比实际情况更复杂。在下面的代码中，*<p>*元素的内容不是单个*Text*节点，实际上是 3 个节点，一个*Text*节点，一个*Element*节点，和另一个*Text*节点。

实时代码：[`jsfiddle.net/domenlightenment/2ZCn3`](http://jsfiddle.net/domenlightenment/2ZCn3)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p>Hi, <strong>cody</strong> welcome!</p>

<script>

var pElement = document.querySelector('p');

console.log(pElement.childNodes.length); *//logs 3*

console.log(pElement.firstChild.data); *// is text node or 'Hi, '*
console.log(pElement.firstChild.nextSibling); *// is Element node or <strong>*
console.log(pElement.lastChild.data); ​*// is text node or ' welcome!'*

</script>
</body>
</html>

```

下一个情况发生在我们以编程方式向我们在代码中创建的元素添加*Text*节点时。在下面的代码中，我创建一个*<p>*元素，然后将两个*Text*节点附加到此元素。这导致了相邻的*Text*节点。

实时代码：[`jsfiddle.net/domenlightenment/jk3Jn`](http://jsfiddle.net/domenlightenment/jk3Jn)

```
<!DOCTYPE html>
<html lang="en">
<body>

<script>

var pElementNode = document.createElement('p');
var textNodeHi = document.createTextNode('Hi ');
var textNodeCody = document.createTextNode('Cody');

pElementNode.appendChild(textNodeHi);
pElementNode.appendChild(textNodeCody);

document.querySelector('div').appendChild(pElementNode);

console.log(document.querySelector('div p').childNodes.length); *//logs 2​*​​​​​​​​​​​​​​​​​

</script>
</body>
</html>

```

## 7.8 使用 *textContent* 删除标记并返回所有子*Text*节点

*textContent*属性可用于获取所有子文本节点，以及将节点的内容设置为特定的*Text*节点。当在节点上使用它来获取节点的文本内容时，它将返回调用该方法的节点中包含的所有文本节点的连接字符串。这个功能将使从 HTML 文档中提取所有文本节点变得非常容易。下面我提取了*<body>*元素中包含的所有文本。请注意，*textContent*不仅收集直接子文本节点，还收集所有子文本节点，无论节点的��装深度如何。

实时代码：N/A

```
<!DOCTYPE html>
<html lang="en">
<body>
<h1> Dude</h2>
<p>you <strong>rock!</strong></p>
<script>

console.log(document.body.textContent); *//logs 'Dude you rock!' with some added white space* </script>
</body>
</html>

```

当使用*textContent*设置节点中包含的文本时，它将首先删除所有子节点，然后用单个*Text*节点替换它们。在下面的代码中，我用单个*Text*节点替换了*<div>*元素内的所有节点。

实时代码：[`jsfiddle.net/domenlightenment/m766T`](http://jsfiddle.net/domenlightenment/m766T)

```
<!DOCTYPE html>
<html lang="en">
<body>
<div>
<h1> Dude</h2>
<p>you <strong>rock!</strong></p>
</div>
<script>

document.body.textContent = 'You don\'t rock!'
console.log(document.querySelector('div').textContent*); *//logs 'You don't rock!'* </script>
</body>
</html>* 
```

*### 注意事项

如果在文档或文档类型节点上使用*textContent*，将返回*null*。

*textContent* 返回*<script>*和*<style>*元素中的内容

## 7.9 *textContent*和*innerText*之间的区别

现代大多数浏览器（除了 Firefox）支持一个看似类似的属性*innerText*，但这些属性并不相同。你应该注意*textContent*和*innerText*之间的以下区别。

+   *innerText*了解 CSS。因此，如果您有隐藏文本，*innerText*会忽略此文本，而*textContent*不会

+   因为*innerText*关心 CSS，它会触发回流，而*textContent*不会

+   *innerText*忽略*<script>*和*<style>*元素中包含的*Text*节点

+   *innerText*，与*textContent*不同，会规范化返回的文本。只需将*textContent*视为返回文档中的内容，其中标记已被移除。这将包括空格、换行和回车符

+   *innerText*被认为是非标准的和特定于浏览器，而*textContent*是根据 DOM 规范实现的

如果您打算使用*innerText*，您将不得不为 Firefox 创建一个解决方法。

## 7.10 使用*normalize()*将兄弟*Text*节点合并为一个文本节点

当文本以编程方式添加到 DOM 时，通常会遇到兄弟*Text*节点。为了消除不包含*Element*节点的兄弟*Text*节点，我们可以使用*normalize()*。这将把 DOM 中的兄弟文本节点连接成一个单一的*Text*节点。在下面的代码中，我创建兄弟文本，将其附加到 DOM，然后对其进行规范化。

实时代码：[`jsfiddle.net/domenlightenment/LG9WR`](http://jsfiddle.net/domenlightenment/LG9WR)

```
<!DOCTYPE html>
<html lang="en">
<body>
<div></div>
<script>

var pElementNode = document.createElement('p');
var textNodeHi = document.createTextNode('Hi');
var textNodeCody = document.createTextNode('Cody');

pElementNode.appendChild(textNodeHi);
pElementNode.appendChild(textNodeCody);

document.querySelector('div').appendChild(pElementNode);

console.log(document.querySelector('p').childNodes.length); *//logs 2*

document.querySelector('div').normalize(); *//combine our sibling text nodes*

console.log(document.querySelector('p').childNodes.length); *//logs 1*

</script>
</body>
</html>

```

## 7.11 使用*splitText()*拆分文本节点

当在*Text*节点上调用*splitText()*时，它将改变被调用的文本节点（保留到偏移量的文本），并返回一个新的*Text*节点，其中包含根据偏移量从原始文本中分离出的文本。在下面的代码中，文本节点*Hey Yo!*在*Hey*后被分割，*Hey*保留在 DOM 中，而*Yo!*被转换为一个新的文本节点并由*splitText()*方法返回。

在线代码：[`jsfiddle.net/domenlightenment/Tz5ce`](http://jsfiddle.net/domenlightenment/Tz5ce)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p>Hey Yo!</p>

<script>

*//returns a new text node, taken from the DOM*
console.log(document.querySelector('p').firstChild.splitText(4).data); *//logs Yo!*

*//What remains in the DOM...*
console.log(document.querySelector('p').firstChild.textContent); *//logs Hey*

</script>
</body>
</html>

```**
