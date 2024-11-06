# 第十一章 - DOM 事件

## 11.1 DOM 事件概述

就 DOM 而言，事件是与 DOM 元素、*document*对象或*window*对象中的元素相关的预定义或自定义时刻。这些时刻通常是预先确定的，并通过将功能（即处理程序/回调）与这些时刻关联起来以在这些时刻发生时执行来进行编程处理。这些时刻可以由 UI 的状态（例如，输入被聚焦或某些内容已被拖动）、运行 JavaScript 程序的环境的状态（例如，页面已加载或 XHR 请求已完成）或程序本身的状态（例如，在页面加载后开始监视用户 UI 交互 30 秒）引发。

可以使用内联属性事件处理程序、属性事件处理程序或*addEventListener()*方法来设置事件。在下面的代码中，我演示了这三种设置事件的模式。这三种模式都添加了一个在鼠标点击 HTML 文档中的*<div>*时调用的*click*事件。

在线代码：[`jsfiddle.net/domenlightenment/4EPjN`](http://jsfiddle.net/domenlightenment/4EPjN)

```
<!DOCTYPE html>
<html lang="en">

*<!-- inline attribure event handler pattern -->*
<body onclick="console.log('fire/trigger attribure event handler')">

<div>click me</div>

<script>
var elementDiv = document.querySelector('div');

*// property event handler pattern*
elementDiv.onclick = function(){console.log('fire/trigger property event handler')};

*//addEventListener method pattern*
elementDiv.addEventListener('click',function(){console.log('fire/trigger addEventListener')}, false);
</script> 
</body>
</html>

```

注意，其中一个事件附加到*<body>*元素。如果您觉得在*<div>*上点击时属性事件处理程序在*<body>*上触发很奇怪，那么请考虑当您点击*<div>*时，您也同时点击了*<body>*元素。在*<div>*以外的任何地方点击，您仍然会看到*<body>*元素上的属性处理程序触发。

虽然这三种将事件附加到 DOM 的程序化模式都安排了事件，但只有*addEventListener()*提供了一个健壮而有组织的解决方案。内联属性事件处理程序混合了 JavaScript 和 HTML，并且最佳实践建议将这些东西分开。

使用属性事件处理程序的缺点是事件属性一次只能分配一个值。也就是说，当将事件分配为属性值时，不能向 DOM 节点添加多个属性事件处理程序。下面的代码通过两次将值分配给*onclick*属性来显示示例，当事件被调用时，使用最后设置的值。

在线代码：[`jsfiddle.net/domenlightenment/U8bWR`](http://jsfiddle.net/domenlightenment/U8bWR)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>
var elementDiv = document.querySelector('div');

*// property event handler* 
elementDiv.onclick = function(){console.log('I\'m first, but I get overidden/replace')}; 
*//overrides/replaces the prior value* elementDiv.onclick = function(){console.log('I win')}; 
</script> 
</body>
</html>

```

此外，使用内联事件处理程序或属性事件处理程序可能会受到作用域细微差别的影响，因为尝试利用由事件调用的函数的作用域链。*addEventListener()*消除了所有这些问题，并将在本章中使用。

### 笔记

*Element*节点通常支持内联事件处理程序（例如*<div onclick=""></div>*）、属性事件处理程序（例如*document.querySelector('div').onclick = function(){}*）和使用*addEventListener()*方法。

*Document* 节点支持属性事件处理程序（例如 *document.onclick = funciton()*）和使用 *addEventListener()* 方法。

*window* 对象支持通过 *<body>* 或 *<frameset>* 元素的内联事件处理程序（例如 *<body onload=""></body>*）、属性事件处理程序（例如 *window.load = function(){}*）以及使用 *addEventListener()* 方法。

属性事件处理程序在历史上被称为“DOM level 0 事件”。*addEventListener()* 经常被称为“DOM level 2 事件”。这相当令人困惑，考虑到并没有 level 0 事件或 level 1 事件。此外，内联事件处理程序被称为“HTML 事件处理程序”。

## 11.2 DOM 事件类型

在下面的表格中，我详细介绍了可以附加到 *Element* 节点、*document* 对象和 *window* 对象的最常见的预定义事件。当然，并非所有事件都直接适用于可以附加到的节点或对象。也就是说，仅仅因为你可以附加事件而不出错，并且很可能调用事件（例如将 *onchange* 事件绑定到 *window*），并不意味着像 *window.onchange* 这样的添加是合乎逻辑的，因为这个事件设计上并不适用于 *window* 对象。

**用户界面事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *load* | *Event*, *UIEvent* | 当资源（HTML 页面、图像、CSS、frameset、*<object>* 或 JS 文件）加载时触发。 | *Element*, *Document*, *window*, *XMLHttpRequest*, *XMLHttpRequestUpload* | 否 | 否 |
| *unload* | *UIEvent* | 当用户代理移除资源（文档、元素、defaultView）或任何依赖资源（图像、CSS 文件等）时触发 | *window*, *<body>*, *<frameset>* | 否 | 否 |
| *abort* | *Event*, *UIEvent* | 当资源（对象/图像）在完全加载之前被停止加载时触发 | *Element*, *XMLHttpRequest*, *XMLHttpRequestUpload* | 是 | 否 |
| *error* | *Event*, *UIEvent* | 当资源加载失败，或已加载但无法根据其语义解释时触发，例如无效图像、脚本执行错误或非格式良好的 XML | *Element*, *XMLHttpRequest*, *XMLHttpRequestUpload* | 是 | 否 |
| *resize* | *UIEvent* | 当文档视图被调整大小时触发。此事件类型在特定事件目标的调整发生后，由用户代理执行所有效果后分发 | *window*, *<body>*, *<frameset>* | 是 | 否 |
| *scroll* | *UIEvent* | 当用户滚动文档或元素时触发。 | *Element*, *Document*, *window* | 是 | 否 |
| *contextmenu* | *MouseEvent* | 通过右键单击元素触发 | *Element* | 是 | 是 |

**焦点事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *blur* | *FocusEvent* | 当元素失去焦点时（通过鼠标或切换标签）触发 | *Element*（除了 *<body>* 和 *<frameseet>* ），*Document* | 否 | 否 |
| *focus* | *FocusEvent* | 当元素获得焦点时触发 | *Element*（除了 *<body>* 和 *<frameseet>* ），*Document* | 否 | 否 |
| *focusin* | *FocusEvent* | 当事件目标即将接收焦点但焦点尚未转移时触发。此事件发生在焦点事件之前 | *Element* | 是 | 否 |
| *focusout* | *FocusEvent* | 当事件目标即将��去焦点但焦点尚未转移时触发。此事件发生在失焦事件之前 | *Element* | 是 | 否 |

**表单事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *change* | 特定于 HTML 表单 | 当控件失去输入焦点且自获得焦点以来其值已被修改时触发 | *Element* | 是 | 否 |
| *reset* | 特定于 HTML 表单 | 当表单被重置时触发 | *Element* | 是 | 否 |
| *submit* | 特定于 HTML 表单 | 当表单被提交时触发 | *Element* | 是 | 是 |
| *select* | 特定于 HTML 表单 | 当用户在文本字段中选择文本时触发，包括输入和文本区域 | *Element* | 是 | 否 |

**鼠标事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *click* | *MouseEvent* | 当鼠标指针在元素上点击（或用户按下回车键）时触发。点击被定义为在相同屏幕位置上按下鼠标和松开鼠标。这些事件的顺序是 *mousedown*>*mouseup*>*click*。根据环境配置，如果在指针设备按钮按下和释放之间发生一个或多个事件类型 *mouseover*、*mousemove* 和 *mouseout*，则可能会分派 *click* 事件。*click* 事件也可能会被 *dblclick* 事件所跟随 | *Element*, *Document*, *window* | 是 | 是 |
| *dblclick* | *MouseEvent* | 当鼠标指针在元素上双击时触发。双击的定义取决于环境配置，除了事件目标在 *mousedown*、*mouseup* 和 *dblclick* 之间必须相同外。如果同时发生单击和双击，则此事件类型必须在 *click* 事件之后分派，否则在 *mouseup* 事件之后分派 | *Element*, *Document*, *window* | 是 | 是 |
| *mousedown* | *MouseEvent* | 当鼠标指针在元素上按下时触发 | *Element*, *Document*, *window* | 是 | 是 |
| *mouseenter* | *MouseEvent* | 当鼠标指针移动到元素或其后代元素的边界上时触发。此事件类型类似于 *mouseover*，但不同之处在于它不冒泡，并且当指针设备从一个元素移动到其后代元素的边界时，*mouseenter* 事件不得分派 | *Element*, *Document*, *window* | 否 | 否 |
| *mouseleave* | *MouseEvent* | 鼠标指针移出元素及其所有后代元素的边界时触发。此事件类型类似于 mouseout，但不同之处在于它不冒泡，并且只有在指针设备离开元素及其所有子元素的边界后才能触发 | *Element*, *Document*, *window* | 否 | 否 |
| *mousemove* | *MouseEvent* | 当鼠标指针在元素上移动时触发。指针设备移动时事件的频率与实现、设备和平台有关，但应为持续指针设备移动触发多个连续的 mousemove 事件，而不是每次鼠标移动的实例都触发单个事件。鼓励实现确定平衡响应性和性能的最佳频率 | *Element*, *Document*, *window* | 是 | 否 |
| *mouseout* | *MouseEvent* | 鼠标指针移出元素的边界时触发。此事件类型类似于*mouseleave*，但不同之处在于它冒泡，并且当指针设备从一个元素移动到其后代元素的边界上时必须触发 | *Element*, *Document*, *window* | 是 | 是 |
| *mouseup* | *MouseEvent* | 鼠标指针按钮释放时在元素上触发 | *Element*, *Document*, *window* | 是 | 是 |
| *mouseover* | *MouseEvent* | 鼠标指针移过元素时触发 | *Element*, *Document*, *window* | 是 | 是 |

**滚轮事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *wheel*（浏览器使用*mousewheel*，但规范使用*wheel*） | *WheelEvent* | 当鼠标滚轮围绕任何轴旋转，或者当等效输入设备（如鼠标球、某些平板电脑或触摸板等）模拟了这样的操作时触发。根据平台和输入设备，对角线滚轮增量可能作为具有多个非零轴的单个滚轮事件传递，或者作为每个非零轴的单独滚轮事件传递。有关浏览器支持的一些有用细节可以在[这里](http://www.quirksmode.org/dom/events/scroll.html)找到。 | *Element*, *Document*, *Window* | 是 | 是 |

**键盘事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *keydown* | *KeyboardEvent* | 当按下键时触发。在执行任何键映射之后发送此事件，但在任何输入法编辑器接收到按键之前发送。对于任何键都会发送此事件，即使它不生成字符代码。 | *Element*, *Document* | 是 | 是 |
| *keypress* | *KeyboardEvent* | 当按下键时触发，但仅当该键通常产生字符值时。这在执行任何按键映射之后发送，但在任何输入法编辑器接收按键之前。 | *元素*，*文档* | 是 | 是 |
| *keyup* | *KeyboardEvent* | 在释放按键时触发。这在执行任何按键映射之后发送，并始终跟随相应的*keydown*和*keypress*事件。 | *元素*，*文档* | 是 | 是 |

**触摸事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *touchstart* | *TouchEvent* | 触发事件以指示用户在触摸表面上放置一个触摸点 | *元素*，*文档*，*窗口* | 是 | 是 |
| *touchend* | *TouchEvent* | 触发事件以指示用户从触摸表面移除一个触摸点，也包括触摸点物理上离开触摸表面的情况，例如被拖出屏幕 | *元素*，*文档*，*窗口* | 是 | 是 |
| *touchmove* | *TouchEvent* | 触发事件以指示用户沿着触摸表面移动一个触摸点 | *元素*，*文档*，*窗口* | 是 | 是 |
| *touchenter* | *TouchEvent* | 触发事件以指示触摸点移入 DOM 元素定义的交互区域 | *元素*，*文档*，*窗口* | 否 | ? |
| *toucheleave* | *TouchEvent* | 触发事件以指示触摸点移出 DOM 元素定义的交互区域 | *元素*，*文档*，*窗口* | 否 | ? |
| *touchcancel* | *TouchEvent* | 触发事件以指示触摸点以实现特定于实现的方式被中断，例如来自 UA 取消触摸的同步事件或操作，或者触摸点离开文档窗口进入能够处理用户交互的非文档区域。 | *元素*，*文档*，*窗口* | 是 | 否 |

### 注意

触摸事件通常仅受 iOS、安卓和黑莓浏览器或可以切换到触摸模式的浏览器（例如 chrome）支持

**窗口，*<body>* 和特定框架的事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *afterprint* | ? | 在对象关联的文档打印或打印预览后立即触发 | *窗口*，*<body>*，*<frameset>* | 否 | 否 |
| *beforeprint* | ? | 在对象关联的文档打印或打印预览之前触发 | *窗口*，*<body>*，*<frameset>* | 否 | 否 |
| *beforeunload* | ? | 在文档被卸载之前触发 | *窗口*，*<body>*，*<frameset>* | 否 | 是 |
| *hashchange* | *HashChangeEvent* | 在 URL 中跟随井号(#)后面的部分发生变化时触发 | *窗口*，*<body>*，*<frameset>* | 否 | 否 |
| *messsage* | ? | 当用户发送跨文档消息或从带有 *postMessage* 的 *Worker* 发送消息时触发。 | *window*, *<body>*, *<frameset>* | 否 | 否 |
| *offline* | *NavigatorOnLine* | 浏览器离线工作时触发。 | *window*, *<body>*, *<frameset>* | 否 | 否 |
| *online* | *NavigatorOnLine* | 浏览器在线工作时触发。 | *window*, *<body>*, *<frameset>* | 否 | 否 |
| *pagehide* | *PageTransitionEvent* | 当从会话历史记录条目遍历到另一个条目时触发。 | *window*, *<body>*, *<frameset>* | 否 | 否 |
| *pageshow* | *PageTransitionEvent* | 当从会话历史记录条目遍历到另一个条目时触发 pagehide 事件。 | *window*, *<body>*, *<frameset>* | 否 | 否 |

**特定于文档的事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *readystatechange* | *Event* | 在 *readyState* 更改时触发事件。 | *Document*, *XMLHttpRequest* | 否 | 否 |
| *DOMContentLoaded* | *Event* | 当网页已解析但尚未完全下载所有资源时触发。 | *Document* | 是 | 否 |

**拖动事件**

| 事件类型 | 事件接口 | 描述 | 事件目标 | 冒泡 | 可取消 |
| --- | --- | --- | --- | --- | --- |
| *drag* | *DragEvent* | 在拖动操作期间在源对象上持续触发。 | *Element*, *Document*, *window* | 是 | 是 |
| *dragstart* | *DragEvent* | 当用户开始拖动文本选择或选定对象时，在源对象上触发。当用户开始拖动鼠标时，会首先触发 ondragstart 事件。 | *Element*, *Document*, *window* | 是 | 是 |
| *dragend* | *DragEvent* | 当用户在拖动操作结束时释放鼠标时，在源对象上触发。 ondragend 事件是最后触发的拖动事件，它在触发在目标对象上的 ondragleave 事件之后触发。 | *Element*, *Document*, *window* | 是 | 否 |
| *dragenter* | *DragEvent* | 当用户将对象拖动到有效的放置目标时，在目标元素上触发。 | *Element*, *Document*, *window* | 是 | 是 |
| *dragleave* | *DragEvent* | 当用户在拖动操作期间将鼠标移出有效的放置目标时，在目标对象上触发。 | *Element*, *Document*, *window* | 是 | 否 |
| *dragover* | *DragEvent* | 当用户将对象拖动到有效的放置目标上方时，在目标元素上持续触发。在 ondragenter 事件触发后，在目标对象上触发 ondragover 事件。 | *Element*, *Document*, *window* | 是 | 是 |
| *drop* | *DragEvent* | 当在拖放操作期间释放鼠标按钮时，在目标对象上触发。在 ondragleave 和 ondragend 事件之前触发 ondrop 事件。 | *Element*, *Document*, *window* | 是 | 是 |

### Notes

下表是根据以下三个资源制作的：[文档对象模型（DOM）3 级事件规范 5 用户事件模块](http://www.w3.org/TR/DOM-Level-3-Events/#events-module)，[DOM 事件参考](https://developer.mozilla.org/en/DOM/DOM_event_reference)，[HTML Living Standard 7.1.6 元素、文档对象和窗口对象上的事件处理程序](http://www.whatwg.org/specs/web-apps/current-work/multipage/webappapis.html#events)，以及[事件兼容性表](http://www.quirksmode.org/dom/events/)。

我在本节中仅提到了最常见的事件类型。请记住，我在本节中排除了许多 HTML5 API（例如，[媒体事件](http://www.whatwg.org/specs/web-apps/current-work/multipage/the-video-element.html#event-definitions)用于*<video>*和*<audio>*元素，或者[XMLHttpRequest Level 2](http://www.w3.org/TR/XMLHttpRequest/#event-handlers)的所有状态更改事件）。

*copy*、*cut*和*textinput*事件未被 DOM 3 事件或 HTML5 定义。

使用 mouseenter 和 mouseleave 代替 mouseover 和 mouseout。不幸的是，Firefox、Chrome 和 Safari 仍未添加这些事件！

## 11.3 事件流

当事件被调用时，[事件通过 DOM 流动或传播](http://www.w3.org/TR/DOM-Level-3-Events/#dom-event-architecture)，在其他节点和 JavaScript 对象上触发相同的事件。事件流可以被编程为发生在捕获阶段（即 DOM 树从树干到树枝）或冒泡阶段（即 DOM 树从树枝到树干），或两者兼而有之。

在下面的代码中，我设置了 10 个事件监听器，所有这些监听器都可以通过在 HTML 文档中的*<div>*元素上点击一次来调用，由于事件流的原因。当点击*<div>*时，捕获阶段从*window*对象开始，沿着 DOM 树向下传播，为每个对象（即*window* **>** *document* **>** *<html>* **>** *<body>* **>** 事件目标）触发*click*事件，直到达到事件目标。一旦捕获阶段结束，目标阶段开始，为目标元素本身触发*click*事件。接下来，传播阶段从事件目标开始向上传播，触发*click*事件，直到达到*window*对象（即事件目标 **>** *<body>* **>** *<html>* **>** *document* **>** *window*）。有了这个知识，很明显为什么��代码示例中点击*<div>*会将 1,2,3,4,5,6,7,8,9,11 记录到控制台。

实时代码：[`jsfiddle.net/domenlightenment/CAdTv`](http://jsfiddle.net/domenlightenment/CAdTv)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me to start event flow</div>

<script>

*/*notice that I am passing the addEventListener() a boolean parameter of true so capture events fire, not just bubbling events*/*

*//1 capture phase*
window.addEventListener('click',function(){console.log(1);},true);

*//2 capture phase*
document.addEventListener('click',function(){console.log(2);},true);

*//3* *capture phase*
document.documentElement.addEventListener('click',function(){console.log(3);},true);

*//4* *capture phase*
document.body.addEventListener('click',function(){console.log(4);},true);

*//5 target phase occurs during capture phase*
document.querySelector('div').addEventListener('click',function(){console.log(5);},true);

*//6 target phase occurs during bubbling phase*
document.querySelector('div').addEventListener('click',function(){console.log(6);},false);

*//7 bubbling phase*
document.body.addEventListener('click',function(){console.log(7);},false);

*//8* *bubbling phase*
document.documentElement.addEventListener('click',function(){console.log(8);},false);

*//9* *bubbling phase*
document.addEventListener('click',function(){console.log(9);},false);

*//10* *bubbling phase*
window.addEventListener('click',function(){console.log(10)},false);

</script> 
</body>
</html>

```

点击*<div>*后，事件流按照以下顺序进行：

1.  捕获阶段在设置为在捕获时触发的窗口上调用点击事件

1.  捕获阶段在设置为在捕获时触发的文档上调用点击事件

1.  捕获阶段在设置为在捕获时触发的 html 元素上调用点击事件

1.  捕获阶段在设置为在捕获时触发的 body 元素上调用点击事件

1.  目标阶段在设置为在捕获时触发的 div 元素上调用点击事件

1.  目标阶段调用设置为冒泡触发的 div 元素上的点击事件

1.  冒泡阶段调用点击事件在 body 元素上设置为冒泡触发

1.  冒泡阶段调用点击事件在 html 元素上设置为冒泡触发

1.  冒泡阶段调用点击事件在文档上设置为冒泡触发

1.  冒泡阶段调用点击事件在窗口上设置为冒泡触发

由于缺乏对此阶段的浏览器支持，使用捕获阶段并不那么常见。通常事件被认为是在冒泡阶段调用的。在下面的代码中，我从上一个代码示例中删除了捕获阶段，并演示了事件调用时通常发生的情况。

实时代码：[`jsfiddle.net/domenlightenment/C6qmZ`](http://jsfiddle.net/domenlightenment/C6qmZ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me to start event flow</div>

<script>

*//1 target phase occurs during bubbling phase*
document.querySelector('div').addEventListener('click',function(){console.log(1);},false);

*//2* *bubbling phase*
document.body.addEventListener('click',function(){console.log(2);},false);

*//3* *bubbling phase*
document.documentElement.addEventListener('click',function(){console.log(3);},false);

*//4* *bubbling phase*
document.addEventListener('click',function(){console.log(4);},false);

*//5* *bubbling phase*
window.addEventListener('click',function(){console.log(5)},false);

</script> 
</body>
</html>

```

注意在最后的代码示例中，如果点击事件是在*<div>*之外的任何地方发起的（点击*<div>*除外），则附加到*<div>*的点击事件不会被调用，冒泡调用会在*<body>*上开始。这是因为事件目标不再是*<div>*，而是*<body>*元素。

### 注意

现代浏览器确实支持使用捕获阶段，因此曾被认为不可靠的东西今天可能会有一些价值。例如，可以在事件目标发生之前拦截事件。

当您阅读本章的事件委托部分时，请将事件捕获和冒泡的知识放在首要位置。

传递给事件监听器函数的事件对象包含一个*eventPhase*属性，其中包含一个数字，指示事件在哪个阶段调用。值为 1 表示捕获阶段。值为 2 表示目标阶段。值为 3 表示冒泡阶段。

## 11.4 向*Element*节点、*window*对象和*Document*对象添加事件监听器

*addEventListener()*方法适用于所有*Element*节点、*window*对象和*document*对象，提供了向 HTML 文档的部分以及与 DOM 和[BOM](https://developer.mozilla.org/en-US/docs/DOM/window)（浏览器对象模型）相关的 JavaScript 对象添加事件监听器的能力。在下面的代码中，我利用这个方法向*<div>*元素、*document*对象和*window*对象添加了一个*mousemove*事件。请注意，由于事件流，鼠标移动特别是在*<div>*上时，每次移动都会调用这三个监听器。

实时代码：[`jsfiddle.net/domenlightenment/sSFK5`](http://jsfiddle.net/domenlightenment/sSFK5)

```
<!DOCTYPE html>
<html lang="en">

<body>

<div>mouse over me</div>

<script>

*//add a mousemove event to the window object, invoking the event during the bubbling phase*
window.addEventListener('mousemove',function(){console.log('moving over window');},false);

*//add a mousemove event to the document object, invoking the event during the bubbling phase*
document.addEventListener('mousemove',function(){console.log('moving over document');},false);

*//add a mousemove event to a <div> element object, invoking the event during the bubbling phase*
document.querySelector('div').addEventListener('mousemove',function(){console.log('moving over div');},false);

</script> 
</body>
</html>

```

上述代码示例中使用的*addEventListener()*方法接受三个参数。第一个参数是要监听的事件类型。请注意，事件类型字符串不包含事件处理程序所需的"on"前缀（即*onmousemove*）。第二个参数是事件发生时要调用的函数。第三个参数是一个布尔值，指示事件是否应在事件流的捕获阶段或冒泡阶段触发。

### 注意

我故意避免讨论内联事件处理程序和属性事件处理程序，而是倡导使用*addEventListener()*。

通常，开发人员希望事件在冒泡阶段触发，以便对象事件处理在将事件冒泡到 DOM 之前处理事件。因此，您几乎总是将*false*值作为*addEventListener()*的最后一个参数提供。在现代浏览器中，如果未指定第三个参数，则默认为 false。

您应该知道*addEventListener()*方法也可以用于*XMLHttpRequest*对象。

## 11.5 移除事件侦听器

如果原始侦听器不是使用匿名函数添加的，则可以使用*removeEventListener()*方法来移除事件侦听器。在下面的代码中，我向 HTML 文档添加了两个事件侦听器，并尝试移除它们。然而，只有使用函数引用附加的侦听器被移除。

实时代码：[`jsfiddle.net/domenlightenment/XP2Ug`](http://jsfiddle.net/domenlightenment/XP2Ug)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click to say hi</div>

<script>

var sayHi = function(){console.log('hi')};

*//adding event listener using anonymous function*
document.body.addEventListener('click',function(){console.log('dude');},false);

*//adding event listener using function reference*
document.querySelector('div').addEventListener('click',sayHi,false);

*//attempt to remove both event listeners, but only the listener added with a funtions reference is removed*
document.querySelector('div').removeEventListener('click',sayHi,false);

*//this of course does not work as the function passed to removeEventListener is a new and different function*
document.body.removeEventListener('click',function(){console.log('dude');},false);

*//clicking the div will still invoke the click event attached to the body element, this event was not removed*

</script> 
</body>
</html>

```

使用*addEventListener()*方法添加的匿名函数无法简单地移除。

## 11.6 从事件对象获取事件属性

事件触发时调用的处理程序或回调函数默认会接收一个包含有关事件本身的所有相关信息的参数。在下面的代码中，我演示了如何访问此事件对象，并记录了加载事件和点击事件的所有属性和值。确保点击*<div*>以查看与点击事件相关的属性。

实时代码：[`jsfiddle.net/domenlightenment/d4SnQ`](http://jsfiddle.net/domenlightenment/d4SnQ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

document.querySelector('div').addEventListener('click',function(event){
Object.keys(event).sort().forEach(function(item){
     console.log(item+' = '+event[item]); *//logs event propeties and values*
});     
},false);

*//assumes 'this' is window*
this.addEventListener('load',function(event){
Object.keys(event).sort().forEach(function(item){
     console.log(item+' = '+event[item]); *//logs event propeties and values*
});     
},false);

</script> 
</body>
</html>

```

请记住，每个事件将根据事件类型（例如[MouseEvent](https://developer.mozilla.org/en/DOM/MouseEvent)、[KeyboardEvent](https://developer.mozilla.org/en/DOM/KeyboardEvent)、[WheelEvent](https://developer.mozilla.org/en/DOM/WheelEvent)）包含略有不同的属性。

### 注意

事件对象还提供*stopPropagation()*、*stopImediatePropagation()*和*preventDefault()*方法。

在本书中，我使用参数名*event*来引用事件对象。事实上，您可以使用任何您喜欢的名称，看到*e*或*evt*也是很常见的。

## 11.7 使用*addEventListener()*时*this*的值

传递给*addEventListener()*方法的事件侦听器函数内部的*this*的值将是事件附加到的节点或对象的引用。在下面的代码中，我将事件附加到一个*<div>*，然后在事件侦听器内部使用*this*来访问事件附加的*<div>*元素。

在线代码：[`jsfiddle.net/domenlightenment/HwKgH`](http://jsfiddle.net/domenlightenment/HwKgH)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

document.querySelector('div').addEventListener('click',function(){
*// 'this' will be the element or node the event listener is attached too*
console.log(this); *//logs '<div>'* 
},false);

</script> 
</body>
</html>

```

当事件作为事件流的一部分被触发时，*this*值将保持事件侦听器附加到的节点或对象的值。在下面的代码中，我们向*<body>*添加了一个*click*事件侦听器，无论您点击*<div>*还是*<body>*，*this*的值始终指向*<body>*。

在线代码：[`jsfiddle.net/domenlightenment/NF2gn`](http://jsfiddle.net/domenlightenment/NF2gn)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

*//click on the <div> or the <body> the value of this remains the <body> element node*
document.body.addEventListener('click',function(){
console.log(this); *//log <body>...</body>*
},false);

</script> 
</body>
</html>

```

另外，可以使用*event.currentTarget*属性来获取相同的引用，即触发事件侦听器的节点或对象，就像*this*属性提供的那样。在下面的代码中，我利用*event.currentTarget*事件对象属性展示它返回与*this*相同的值。

在线代码：[`jsfiddle.net/domenlightenment/uQm3f`](http://jsfiddle.net/domenlightenment/uQm3f)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

document.addEventListener('click',function(event){
console.log(event.currentTarget);  *//logs '#document'
//same as...* console.log(this);
},false);

document.body.addEventListener('click',function(event){
console.log(event.currentTarget); *//logs '<body>'
//same as...* console.log(this);
},false);

document.querySelector('div').addEventListener('click',function(event){
console.log(event.currentTarget); *//logs '<div>'*
*//same as...*
console.log(this);
},false);

</script> 
</body>
</html>

```

## 11.8 引用事件的*target*而不是触发事件的节点或对象

因为事件流的存在，可能会点击包含在*<body>*元素内部的*<div>*，并且触发附加到*<body>*元素的*click*事件侦听器。当这种情况发生时，传递给附加到*<body>*的事件侦听器函数的事件对象（即*event.target*）提供了对产生事件的节点或对象的引用（即目标）。在下面的代码中，当点击*<div>*时，将调用*<body>*元素的*click*事件侦听器，并且*event.target*属性引用了原始的*<div>*，即点击事件的目标。当事件因事件流而触发时，*event.target*可以非常有用，以获取有关事件来源的知识。

在线代码：[`jsfiddle.net/domenlightenment/dGkTQ`](http://jsfiddle.net/domenlightenment/dGkTQ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

document.body.addEventListener('click',function(event){
*//when the <div> is clicked logs '<div>' because the <div> was the target in the event flow*
console.log(event.target); 
},false);

</script> 
</body>
</html>

```

请考虑，在我们的代码示例中，如果点击*<body>*元素而不是*<div>*，那么事件*target*和事件侦听器被调用的元素节点将是相同的。因此，*event.target*、*this*和*event.currentTarget*都将包含对*<body>*元素的引用。

## 11.9 使用*preventDefault()*取消默认浏览器事件

当向用户呈现 HTML 页面时，浏览器提供了几个已经连接的事件。例如，单击链接具有相应的事件（即导航到 URL）。单击复选框也是如此（即选中框），或者在文本字段中输入文本（即输入文本并显示在屏幕上）。这些浏览器事件可以通过在与调用浏览器默认事件的节点或对象相关联的事件处理程序函数中调用*preventDefault()*方法来阻止。在下面的代码中，我阻止了发生在*<a>*、*<input>*和*<textarea>*上的默认事件。

live code: [`jsfiddle.net/domenlightenment/Ywcyh`](http://jsfiddle.net/domenlightenment/Ywcyh)

```
<!DOCTYPE html>
<html lang="en">
<body>

<a href="google.com">no go</div>

<input type="checkbox" />

<textarea></textarea>

<script>

document.querySelector('a').addEventListener('click',function(event){
event.preventDefault(); *//stop the default event for <a> which would be to load a url*
},false);

document.querySelector('input').addEventListener('click',function(event){
event.preventDefault(); *//stop default event for checkbox, which would be to toggle checkbox state*
},false);

document.querySelector('textarea').addEventListener('keypress',function(event){
event.preventDefault(); *//stop default event for textarea, which would be to add characters typed*
},false);

*/*keep in mind that events still propagate, clicking the link in this html document will stop the default event but not event bubbling*/*
document.body.addEventListener('click',function(){
console.log('the event flow still flows!');
},false);

</script> 
</body>
</html>

```

在上一个代码示例中，尝试单击链接、选中复选框或在文本输入中键入文本将失败，因为我正在阻止这些元素的默认事件发生。

### 注意

*preventDefault()*方法不会阻止事件传播（即冒泡或捕获阶段）

在事件监听器主体末尾提供一个*return false*与调用*preventDefault()*方法具有相同的效果

传递给事件监听器函数的事件对象包含一个布尔值*cancelable*属性，该属性指示事件是否会响应*preventDefault()*方法并取消默认行为

传递给事件监听器函数的事件对象包含一个*defaultPrevented*属性，如果对冒泡事件调用了*preventDefault()*，则该属性为 true。

## 11.10 使用*stopPropagation()*停止事件流

从事件处理程序/监听器内部调用*stopProgagation()*将停止捕获和冒泡事件流阶段，但仍将调用直接附加到节点或对象的任何事件。在下面的代码中，由于我们阻止了事件冒泡到*<body>*上的*onclick*事件，因此*<body>*上的*onclick*事件永远不会被调用。

live code: [`jsfiddle.net/domenlightenment/RFKmA`](http://jsfiddle.net/domenlightenment/RFKmA)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

document.querySelector('div').addEventListener('click',function(){
console.log('me too, but nothing from the event flow!');
},false);

document.querySelector('div').addEventListener('click',function(event){
console.log('invoked all click events attached, but cancel capture and bubble event phases');
event.stopPropagation();
},false);

document.querySelector('div').addEventListener('click',function(){
console.log('me too, but nothing from the event flow!');
},false);

*/*when the <div> is clicked this event is not invoked because one of the events attached to the <div> stops the capture and bubble flow.*/*
document.body.addEventListener('click',function(){
console.log('What, denied from being invoked!');
},false);

</script> 
</body>
</html>

```

请注意，仍会调用附加到*<div>*的其他点击事件！此外，使用*stopPropagation()*不会阻止默认事件。如果我们的代码示例中的*<div>*是一个带有 href 值的*<a>*，调用 stopPropagation 将不会阻止浏览器默认事件的调用。

## 11.11 使用*stopImmediatePropagation()*停止事件流以及目标上的其他类似事件

在事件处理程序/监听器内部调用*stopImmediatePropagation()*将停止事件流阶段（即*stopPropagation()*），以及任何其他类似事件，这些事件附加到在调用*stopImmediatePropagation()*方法的事件监听器之后的事件目标上。在下面的代码示例中，如果我们从附加到*<div>*的第二个事件监听器中调用*stopImmediatePropagation()*，则接下来的点击事件将不会被调用。

实时代码：[`jsfiddle.net/domenlightenment/znSjM`](http://jsfiddle.net/domenlightenment/znSjM)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>

<script>

*//first event attached*
document.querySelector('div').addEventListener('click',function(){
console.log('I get invoked because I was attached first');
},false);

*//seond event attached*
document.querySelector('div').addEventListener('click',function(event){
console.log('I get invoked, but stop any other click events on this target');
event.stopImmediatePropagation();
},false);
 *//third event attached, but because stopImmediatePropagation() was called above this event does not get invoked*
document.querySelector('div').addEventListener('click',function(){
console.log('I get stopped from the previous click event listener');
},false);

*//notice that the event flow is also cancelled as if stopPropagation was called too*
document.body.addEventListener('click',function(){
console.log('What, denied from being invoked!');
},false);

</script> 
</body>
</html>

```

### 注意

使用*stopImmediatePropagation()*并不能阻止默认事件。浏览器默认事件仍然会被调用，只有调用*preventDefault()*才能停止这些事件。

## 11.12 自定义事件

开发人员不仅限于预定义的事件类型。可以使用*addEventListener()*方法像平常一样结合*document.createEvent()*、*initCustomEvent()*和*dispatchEvent()*来附加和调用自定义事件。在下面的代码中，我创建了一个名为*goBigBlue*的自定义事件并调用了该事件。

实时代码：[`jsfiddle.net/domenlightenment/fRndj`](http://jsfiddle.net/domenlightenment/fRndj)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>click me</div>​​​​​

<script>

var divElement = document.querySelector('div');

*//create the custom event*
var cheer = document.createEvent('CustomEvent'); *//the 'CustomEvent' parameter is required*

*//create an event listener for the custom event*
divElement.addEventListener('goBigBlue',function(event){
    console.log(event.detail.goBigBlueIs)
},false);

*/*Use the initCustomEvent method to setup the details of the custom event.
Parameters for initCustomEvent are: (event, bubble?, cancelable?, pass values to event.detail)*/*
cheer.initCustomEvent('goBigBlue',true,false,{goBigBlueIs:'its gone!'});
     *//invoke the custom event using dispatchEvent*
divElement.dispatchEvent(cheer);​

</script> 
</body>
</html>

```

### 注意

IE9 要求（不是可选的）*initiCustomEvent()*的第四个参数

[DOM 4 规范添加了一个*CustomEvent()*构造函数](http://dvcs.w3.org/hg/domcore/raw-file/tip/Overview.html#interface-customevent)，简化了自定义事件的生命周期，但在 ie9 中不受支持，在撰写本文时仍在变化中。

## 11.13 模拟/触发鼠标事件

模拟事件与创建自定义事件并没有太大不同。在模拟鼠标事件的情况下，我们使用*document.createEvent()*创建一个*'MouseEvent'*。然后，使用*initMouseEvent()*设置即将发生的鼠标事件。接下来，将鼠标事件分派到我们想要模拟事件的元素上（即 html 文档中的*<div>*）。在下面的代码中，一个点击事件被附加到页面中的*<div>*上。而不是点击*<div>*来调用点击事件，事件是通过程序化地设置鼠标事件并将事件分派到*<div>*来触发或模拟的。

实时代码：[`jsfiddle.net/domenlightenment/kx7zJ`](http://jsfiddle.net/domenlightenment/kx7zJ)

```
<!DOCTYPE html>
<html lang="en">
<body>

<div>no need to click, we programatically trigger it</div>​​​​

<script>

var divElement = document.querySelector('div');

*//setup click event that will be simulated*
divElement.addEventListener('click',function(event){
    console.log(Object.keys(event));
},false);

*//create simulated mouse event 'click'*
var simulateDivClick = document.createEvent('MouseEvents');

*/*setup simulated mouse 'click'
initMouseEvent(type,bubbles,cancelable,view,detail,screenx,screeny,clientx,clienty,ctrlKey,altKey,shiftKey,metaKey,button,relatedTarget)**
simulateDivClick.initMouseEvent('click',true,true,document.defaultView,0,0,0,0,0,false,false,false,0,null,null);

*//invoke simulated clicked event*
divElement.dispatchEvent(simulateDivClick);

</script> 
</body>
</html>

```

### 注意

在撰写本文时，模拟/触发鼠标事件在所有现代浏览器中都有效。模拟其他类型的事件很快变得更加复杂，需要利用[simulate.js](https://github.com/airportyh/simulate.js)或 jQuery（例如 jQuery 的*trigger()*方法）。

## 11.14 事件委托

事件委托，简单地说，是利用事件流和单个事件监听器来处理多个事件目标的编程行为。事件委托的一个副作用是，事件目标在事件创建时不必在 DOM 中，也能响应事件。这在处理更新 DOM 的 XHR 响应时非常方便。通过实现事件委托，添加到 DOM 中的新内容在 JavaScript 加载解析后可以立即开始响应事件。想象一下，你有一个拥有无限行和列的表格。使用事件委托，我们可以为*<table>*节点添加一个单个事件监听器，作为事件的初始目标的委托。在下面的代码示例中，点击任何一个*<td>*（即事件的目标）将把它的事件委托给*<table>*上的*click*监听器。不要忘记，所有这些都是因为事件流，特别是冒泡阶段，才变得可能。

在线代码：[`jsfiddle.net/domenlightenment/BRkVL`](http://jsfiddle.net/domenlightenment/BRkVL)

```
<!DOCTYPE html>
<html lang="en">
<body>

<p>Click a table cell</p>

<table border="1">
    <tbody>
        <tr><td>row 1 column 1</td><td>row 1 column 2</td></tr>
        <tr><td>row 2 column 1</td><td>row 2 column 2</td></tr>
        <tr><td>row 3 column 1</td><td>row 3 column 2</td></tr>
        <tr><td>row 4 column 1</td><td>row 4 column 2</td></tr>
        <tr><td>row 5 column 1</td><td>row 5 column 2</td></tr>
        <tr><td>row 6 column 1</td><td>row 6 column 2</td></tr>
    </tbody>
</table>​​​​​​​​

<script>

document.querySelector('table').addEventListener('click',function(event){
	if(event.target.tagName.toLowerCase() === 'td'){ *//make sure we only run code if a td is the target*
		console.log(event.target.textContent); *//use event.target to gain access to target of the event which is the td* 
	}      
},false);

</script> 
</body>
</html>

```

如果我们在代码示例中更新表格以添加新行，新行将在渲染到屏幕上后立即响应*click*事件，因为*click*事件被委托给了*<table>*元素节点。

### 注意

事件委托在处理*click*、*mousedown*、*mouseup*、*keydown*、*keyup*和*keypress*事件类型时是理想的选择。
