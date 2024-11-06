# 11 互动游戏作为反应系统

|     11.1 关于反应式动画 |
| --- |
|     11.2 前提条件 |
|     11.3 版本：飞机横穿屏幕移动 |
|       11.3.1 更新世界状态 |
|       11.3.2 显示世界状态 |
|       11.3.3 观察时间（以及组合各部分） |
|     11.4 版本：环绕 |
|     11.5 版本：下降 |
|       11.5.1 移动飞机 |
|       11.5.2 绘制场景 |
|       11.5.3 收尾工作 |
|     11.6 版本：响应按键 |
|     11.7 版本：着陆 |
|     11.8 版本：一个固定的气球 |
|     11.9 版本：留意油箱 |
|     11.10 版本：气球也在移动 |
|     11.11 版本：一，二，......，九十九个气球！ |

在本教程中，我们将编写一个小型交互式游戏。 游戏不会很复杂，但它将具有构建自己更丰富游戏所需的所有元素。

想象一下我们有一架飞机要着陆。 不幸的是，它正试图在一个热气球节期间这样做，所以自然而然地想要避免与任何（移动的）气球相撞。此外，既有陆地又有水域，飞机需要在陆地上降落。我们可能还会为其配备有限的燃料来完成任务。以下是游戏的一些动画：

+   [`world.cs.brown.edu/1/projects/flight-lander/v9-success.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v9-success.swf)

    飞机成功着陆。

+   [`world.cs.brown.edu/1/projects/flight-lander/v9-collide.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v9-collide.swf)

    噢——<wbr>飞机与气球相撞！

+   [`world.cs.brown.edu/1/projects/flight-lander/v9-sink.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v9-sink.swf)

    噢——<wbr>飞机降落在水里！

到最后，你将编写这个程序的所有相关部分。你的程序将：使飞机自主移动；检测按键并相应调整飞机；有多个移动的气球；检测飞机和气球之间的碰撞；检查是否降落在水和陆地上；并考虑燃料的使用。哦，这涉及到很多事情！因此，我们不会一次性写完所有内容；相反，我们将逐步构建。但最终我们会完成的。

## 11.1 关于反应性动画

我们正在编写一个具有两个重要交互元素的程序：它是一个动画，意味着它给人以运动的印象，它是反应性的，意味着它对用户输入做出响应。这两者都可能很难编程，但 Pyret 提供了一个简单的机制，可以同时适应这两者，并与其他编程原则（如测试）很好地集成。我们将在学习过程中了解这一点。

创建动画的关键是电影原理。即使在你观看的最复杂的电影中，也没有运动（事实上，“电影”这个术语——<wbr>缩写为“moving picture”——<wbr>是一个巧妙的虚假广告）。相反，只是一系列快速连续显示的静止图像，依靠人类大脑产生运动的印象。我们将利用相同的想法：我们的动画将由一系列单独的图像组成，我们将要求 Pyret 快速连续显示这些图像。然后我们将看到反应性如何融入同一过程中。

## 11.2 准备工作

首先，我们应该告诉 Pyret 我们打算使用图像和动画。我们加载库如下：

```
import image as I
import world as W
```

这告诉 Pyret 加载这两个库并将结果绑定到相应的名称 I 和 W。因此，所有图像操作都来自 I，动画操作来自 W。

## 11.3 版本：飞机横穿屏幕移动

我们将从最简单的版本开始：飞机在屏幕上水平移动。观看这个视频：

[`world.cs.brown.edu/1/projects/flight-lander/v1.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v1.swf)

首先，这是一架飞机的图像：找到你喜欢的飞机图像！但不要花太多时间在上面，因为我们还有很多工作要做。

[`world.cs.brown.edu/1/clipart/airplane-small.png`](http://world.cs.brown.edu/1/clipart/airplane-small.png)

我们可以告诉 Pyret 加载这个图像并给它一个名称如下：

```
AIRPLANE-URL =
  "http://world.cs.brown.edu/1/clipart/airplane-small.png"
AIRPLANE = I.image-url(AIRPLANE-URL)
```

因此，当我们提到飞机时，它将始终指代这个图像。（在交互区域试试吧！）

现在再看一次视频。观察不同时间点发生的事情。什么保持不变，什么发生了变化？共同之处是水和陆地，它们保持不变。发生变化的是飞机的（水平）位置。

注意

> 世界状态包括一切变化的事物。保持不变的事物不需要记录在世界状态中。

现在我们可以定义我们的第一个世界状态：

世界定义

> 世界状态是一个数字，表示飞机的 x 位置。

注意上面的一些重要事项。

注意

> 当我们记录世界状态时，我们不仅捕获值的类型，还捕获它们的预期含义。

现在我们有了核心数据的表示，但是要生成上述动画，我们仍然需要做一些事情：

1.  请求在时间流逝时通知您。

1.  随着时间的推移，相应地更新世界状态。

1.  给定更新的世界状态，生成相应的视觉显示。

这听起来像是很多！幸运的是，Pyret 使这比听起来容易得多。我们将以略有不同的顺序进行这些操作，而不是按照上面列出的顺序。

### 11.3.1 更新世界状态

正如我们所指出的，飞机实际上并没有“移动”。相反，我们可以要求 Pyret 在每次时钟滴答（[REF]）时通知我们。如果在每个滴答中我们以适当不同的位置放置飞机，并且滴答发生得足够频繁，我们将得到运动的印象。

因为世界状态只包括飞机的 x 位置，所以要将其向右移动，我们只需增加其值。让我们首先给这个恒定的距离起个名字：

```
AIRPLANE-X-MOVE = 10
```

我们将需要编写一个反映此移动的函数。让我们首先编写一些测试用例：

```
check:
  move-airplane-x-on-tick(50) is 50 + AIRPLANE-X-MOVE
  move-airplane-x-on-tick(0) is 0 + AIRPLANE-X-MOVE
  move-airplane-x-on-tick(100) is 100 + AIRPLANE-X-MOVE
end
```

现在函数的定义很清楚了：

```
fun move-airplane-x-on-tick(w):
  w + AIRPLANE-X-MOVE
end
```

确实，Pyret 将确认此函数是否通过了其所有测试。注意

> 如果您有编程动画和响应式程序的先验经验，您会立即注意到一个重要的区别：在 Pyret 中很容易测试程序的各个部分！

### 11.3.2 显示世界状态

现在我们准备绘制游戏的视觉输出。我们生成一个包含所有必要组件的图像。首先帮助定义一些表示视觉输出的常量：

```
WIDTH = 800
HEIGHT = 500

BASE-HEIGHT = 50
WATER-WIDTH = 500
```

使用这些，我们可以创建一个空白画布，并覆盖表示水和陆地的矩形：

```
BLANK-SCENE = I.empty-scene(WIDTH, HEIGHT)

WATER = I.rectangle(WATER-WIDTH, BASE-HEIGHT, "solid", "blue")
LAND = I.rectangle(WIDTH - WATER-WIDTH, BASE-HEIGHT, "solid", "brown")

BASE = I.beside(WATER, LAND)

BACKGROUND =
  I.place-image(BASE,
    WIDTH / 2, HEIGHT - (BASE-HEIGHT / 2),
    BLANK-SCENE)
```

检查交互区域中背景的值，以确认它看起来是否正确。

> 现在就做！
> 
> > 当我们放置基地时，将其除以二是因为 Pyret 将图像的中心放在给定的位置。删除该除法，看看结果图像会发生什么。

现在我们知道如何获得我们的背景了，我们准备将飞机放在上面。执行此操作的表达式大致如下：

```
I.place-image(AIRPLANE,
  # some x position,
  50,
  BACKGROUND)
```

但我们要使用什么 x 位置呢？实际上，这就是世界状态所代表的！所以我们根据这个表达式创建一个函数：

```
fun place-airplane-x(w):
  I.place-image(AIRPLANE,
    w,
    50,
    BACKGROUND)
end
```

### 11.3.3 观察时间（并组合这些部分）

最后，我们准备将这些部分组合在一起。我们调用一个名为 big-bang 的函数，它创建动画。 big-bang 需要提供一个初始世界状态以及告诉它如何反应的处理程序。指定 on-tick 告诉 Pyret 运行一个时钟，并且每次时钟滴答（大约每秒三十次）时调用相关的处理程序。 to-draw 处理程序由 Pyret 用于刷新可视显示。因此：

```
W.big-bang(0, [list:
    W.on-tick(move-airplane-x-on-tick),
    W.to-draw(place-airplane-x)])
```

创建一个运行程序，飞机在背景中飞行！

就是这样！我们创建了我们的第一个动画。既然我们已经把所有的准备工作都做好了，我们可以开始增强它了。

> 练习
> 
> > 如果你希望飞机看起来移动得更快，你可以改变什么？

## 11.4 版本：环绕

当你运行上述程序时，你会注意到过了一会儿，飞机就消失了。这是因为它已经超过了屏幕的右边缘；它仍在“被绘制”，但是在你看不到的位置。这不太有用！另外，过了一段时间后，您可能会收到错误提示，因为计算机要求在图形系统无法管理的位置绘制飞机。相反，当飞机即将超过屏幕的右边缘时，我们希望它以相应的量重新出现在左边：“环绕”，如同。

这是此版本的视频：

[`world.cs.brown.edu/1/projects/flight-lander/v2.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v2.swf)

让我们想想我们需要改变什么。显然，我们需要修改更新飞机位置的函数，因为现在这必须反映我们决定循环的决定。但是绘制飞机的任务根本不需要改变！同样，世界状态的定义也不需要改变。

因此，我们只需要修改 move-airplane-x-on-tick。函数 num-modulo 正是我们需要的。也就是说，我们希望 x 位置始终对场景的宽度取模：

```
fun move-airplane-wrapping-x-on-tick(x):
  num-modulo(x + AIRPLANE-X-MOVE, WIDTH)
end
```

注意，我们可以简单地重用上一个定义的内容，而不是复制它的内容：

```
fun move-airplane-wrapping-x-on-tick(x):
  num-modulo(move-airplane-x-on-tick(x), WIDTH)
end
```

这使我们的意图更加清晰：计算我们之前可能有的任何位置，但适应坐标以保持在场景宽度内。

那是一个提出的重新定义。一定要彻底测试这个函数：它比你想的要棘手！你考虑过所有情况吗？例如，如果飞机正好在屏幕右边缘的一半怎么办？

注意

> 可以保持不变 move-airplane-x-on-tick 并在 place-airplane-x 中执行模数运算。我们选择不这样做的原因如下。在这个版本中，我们真的认为飞机是在周围盘旋并从左边缘重新开始（想象世界是一个圆柱体...）。因此，飞机的 x 位置确实会不断回落。如果相反地，我们允许世界状态单调增加，那么它实际上将表示已行进的总距离，这与我们对世界状态的定义相矛盾。

## 11.5 版本：下降

当然，我们需要我们的飞机在更多的维度上移动：为了到达最终的游戏，它必须上升和下降。现在，我们将专注于这个最简单的版本，即持续下降的飞机。这是一个视频：

[`world.cs.brown.edu/1/projects/flight-lander/v3.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v3.swf)

让我们再次考虑这个视频的各个帧。什么是不变的？再次是水和陆地。什么在变化？飞机的位置。但是，以前飞机只在 x 维度移动，现在它在 x 和 y 两个维度上移动。这立即告诉我们，我们对世界状态的定义是不充分的，必须修改。

因此，我们定义一个新的结构来保存这对数据：

```
data Posn:
  | posn(x, y)
end
```

有了这个，我们可以修改我们的定义：世界定义

> 世界状态是一个位置，表示飞机在屏幕上的 x 位置和 y 位置。

### 移动飞机

首先，让我们考虑 move-airplane-wrapping-x-on-tick。以前我们的飞机只在 x 方向移动；现在我们希望它也下降，这意味着我们必须向当前 y 值添加一些内容：

```
AIRPLANE-Y-MOVE = 3
```

让我们为新函数编写一些测试用例。这是其中一个：

```
check:
  move-airplane-xy-on-tick(posn(10, 10)) is posn(20, 13)
end
```

另一种编写测试的方法是：

```
check:
  p = posn(10, 10)
  move-airplane-xy-on-tick(p) is
    posn(move-airplane-wrapping-x-on-tick(p.x),
      move-airplane-y-on-tick(p.y))
end
```

注意

> 哪种编写测试的方法更好？都好！它们各自提供不同的优势：
> 
> +   前一种方法的好处在于非常具体：你期望什么没有疑问，并且它表明你确实可以从第一原理计算出所需的答案。
> +   
> +   后一种方法的优势在于，如果您更改程序中的常量（例如下降速率），看似正确的测试不会突然失败。也就是说，这种形式的测试更多地涉及事物之间的关系，而不是它们的精确值。
> +   
> 还有另一种选择，通常结合了两种方法的优点：尽可能具体地编写答案（前一种风格），但使用常量来计算答案（后一种风格的优势）。例如：
> 
> ```
> check:
>   p = posn(10, 10)
>   move-airplane-xy-on-tick(p) is
>    posn(num-modulo(p.x + AIRPLANE-X-MOVE, WIDTH),
>     p.y + AIRPLANE-Y-MOVE)
> end
> ```
> 
> 练习
> 
> > 在继续之前，你写了足够的测试用例吗？你确定吗？例如，你测试过飞机在屏幕边缘时应该发生什么情况吗？我们觉得没有 —— 在继续之前回去写更多的测试吧！

使用设计配方，现在定义 move-airplane-xy-on-tick。你应该得到类似这样的东西：

```
fun move-airplane-xy-on-tick(w):
  posn(move-airplane-wrapping-x-on-tick(w.x),
    move-airplane-y-on-tick(w.y))
end
```

请注意，我们重新使用了现有函数的 x 维度，并相应地为 y 维度创建了一个辅助函数：

```
fun move-airplane-y-on-tick(y):
  y + AIRPLANE-Y-MOVE
end
```

目前这可能有点过分，但它确实导致了责任分离的更清晰，使得每个维度的运动复杂性可以独立演变，同时保持代码相对可读性。

### 绘制场景

我们还必须检查并更新 place-airplane-x。我们之前的定义将飞机放在一个任意的 y 坐标上；现在我们必须从世界状态中取得 y 坐标：fun place-airplane-xy(w): I.place-image(AIRPLANE, w.x, w.y, BACKGROUND) end 请注意，我们实际上不能重用以前的定义，因为它硬编码了 y 位置，而我们现在必须将其作为参数。

### 完善细节

我们完成了吗？看起来是这样：我们已经检查了所有消耗和产生世界状态的过程，并相应地更新了它们。实际上，我们忘了一件小事：big-bang 给出的初始世界状态！如果我们改变了世界状态的定义，那么我们也需要重新考虑这个参数。（我们还需要传递新的处理程序而不是旧的处理程序。）

```
INIT-POS = posn(0, 0)

W.big-bang(INIT-POS, [list:
    W.on-tick(move-airplane-xy-on-tick),
    W.to-draw(place-airplane-xy)])
```

> 练习
> 
> > 飞机被屏幕截断有点不尽如人意。您可以使用 I.image-width 和 I.image-height 获取图像（如飞机）的尺寸。在初始场景中确保飞机完全适合屏幕，并在 move-airplane-xy-on-tick 中同样如此。

## 11.6 版本：响应按键

现在我们让飞机下降，它也没有理由不能上升。这是一个视频：

[`world.cs.brown.edu/1/projects/flight-lander/v4.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v4.swf)

我们将使用键盘来控制它的运动：具体来说，按下上键将使其向上移动，而按下下键将使其更快地下降。使用我们已经知道的知识很容易支持这一点：我们只需要使用 W.on-key 提供另一个处理程序。这个处理程序接受两个参数：第一个是世界的当前值，第二个是表示按下的键的表示。对于这个程序来说，我们关心的唯一键值是 "up" 和 "down"。

让我们定义一个常量来表示按键代表多少距离：

```
KEY-DISTANCE = 10
```

现在我们可以定义一个函数，根据按下的键的不同改变飞机的位置：

```
fun alter-airplane-y-on-key(w, key):
  ask:
    | key == "up"   then: posn(w.x, w.y - KEY-DISTANCE)
    | key == "down" then: posn(w.x, w.y + KEY-DISTANCE)
    | otherwise: w
  end
end
```

> 现在就去做吧！
> 
> > 为什么这个函数定义包含
> > 
> > ```
> > | otherwise: w
> > ```
> > 
> > 作为它的最后一个条件？

注意，如果我们收到的键不是我们期望的两个键之一，我们将保持世界状态不变；从用户的角度来看，这就等效于忽略按键。删除这最后一条子句，按下其他键，看看会发生什么！

无论你选择什么，一定要测试一下！飞机会不会漂移到屏幕的顶部？底部的屏幕呢？它会与陆地或水重叠吗？

一旦我们编写并彻底测试了这个函数，我们只需要要求 Pyret 使用它来处理按键：

```
W.big-bang(INIT-POS, [list:
    W.on-tick(move-airplane-xy-on-tick),
    W.on-key(alter-airplane-y-on-key),
    W.to-draw(place-airplane-xy)])
```

现在你的飞机不仅随着时间的流逝而移动，还会对你的按键作出响应。你可以让它永远保持在空中！

## 11.7 版本：着陆

记住，我们游戏的目标是让飞机着陆，而不是让它无限期地保持在空中。这意味着我们需要检测飞机何时达到陆地或水平面，并在达到时终止动画：

[`world.cs.brown.edu/1/projects/flight-lander/v5.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v5.swf)

首先，让我们尝试描述动画何时应该停止。这意味着编写一个函数，接受当前的世界状态并产生一个布尔值：如果动画应该停止，则为 true，否则为 false。这需要一点基于飞机大小的算术：

```
fun is-on-land-or-water(w):
  w.y >= (HEIGHT - BASE-HEIGHT)
end
```

我们还可以告诉 Pyret 使用这个谓词自动停止动画：

```
W.big-bang(INIT-POS, [list:
    W.on-tick(move-airplane-xy-on-tick),
    W.on-key(alter-airplane-y-on-key),
    W.to-draw(place-airplane-xy),
    W.stop-when(is-on-land-or-water)])
```

> 练习
> 
> > 当你测试这个时，你会发现它不太正确，因为它没有考虑到飞机图像的大小。结果，飞机只有在进入陆地或水域一半时才会停止，而不是在第一次接触时停止。调整公式，使其在第一次接触时停止。
> > 
> 练习
> 
> > 将此扩展，使飞机在接触陆地后滚动一段时间，根据物理定律减速。
> > 
> 练习
> 
> > 假设飞机实际上正在降落到一个秘密的地下空军基地。实际的着陆跑道实际上在地面以下，并且只有当飞机着陆时才会打开。这意味着，着陆后，只有突出地面以上的飞机部分才会可见。实现这个。作为提示，考虑修改 place-airplane-xy。

## 11.8 版本：一个固定的气球

现在让我们在场景中添加一个气球。这是一个动作的视频：

[`world.cs.brown.edu/1/projects/flight-lander/v6.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v6.swf)

请注意，当飞机移动时，一切都——包括气球——保持静止。因此，我们不需要改变世界状态来记录气球的位置。我们需要做的只是改变程序终止的条件：实际上，有一种情况下它会终止，那就是与气球碰撞。

游戏何时终止？现在有两种情况：一种是与陆地或水域接触，另一种是与气球接触。前者与之前的情况相同，因此我们可以专注于后者。

气球在哪里，我们如何表示它在哪里？后者很容易回答：这就是 posns 的用处。至于前者，我们可以决定它在哪里：

```
BALLOON-LOC = posn(600, 300)
```

或者我们可以让 Pyret 选择一个随机位置：

```
BALLOON-LOC = posn(random(WIDTH), random(HEIGHT))
```

> 练习
> 
> > 改进气球的随机放置，使其位于可信的空间（例如，不要被淹没）。

给定气球的位置，我们只需要检测碰撞。一种简单的方法是：确定飞机和气球之间的距离是否在某个阈值内：

```
fun are-overlapping(airplane-posn, balloon-posn):
  distance(airplane-posn, balloon-posn)
    < COLLISION-THRESHOLD
end
```

其中 COLLISION-THRESHOLD 是根据飞机和气球图像的大小计算出的某个合适的常数。（对于这些特定图像，75 效果非常好。）距离是什么？它接受两个 posns 并确定它们之间的欧几里德距离：

```
fun distance(p1, p2):
  fun square(n): n * n end
  num-sqrt(square(p1.x - p2.x) + square(p1.y - p2.y))
end
```

最后，我们必须将两个终止条件编织在一起：

```
fun game-ends(w):
  ask:
    | is-on-land-or-water(w)      then: true
    | are-overlapping(w, BALLOON) then: true
    | otherwise: false
  end
end
```

并使用它代替：

```
W.big-bang(INIT-POS, [list:
    W.on-tick(move-airplane-xy-on-tick),
    W.on-key(alter-airplane-y-on-key),
    W.to-draw(place-airplane-xy),
    W.stop-when(game-ends)])
```

> 现在开始！
> 
> > 你看到如何更简洁地编写游戏结束了吗？

这是另一个版本：

```
fun game-ends(w):
  is-on-land-or-water(w) or are-overlapping(w, BALLOON-LOC)
end
```

## 11.9 版本：保持眼睛在油箱上

现在我们将介绍燃料的概念。在我们简化的世界中，燃料不是下降所必需的—<wbr>重力会自动做到—<wbr>但它是爬升所需的。我们假设燃料以整数单位计数，并且每次上升都会消耗一单位的燃料。当你耗尽燃料时，程序不再响应向上箭头，因此你将无法避开气球或水。

在过去，我们曾查看游戏视频的静止图像，以确定什么在变化，什么不在变化。对于这个版本，我们可以很容易地在屏幕上放置一个小表来显示剩余燃料的数量。但我们故意没有这样做，以说明一个原则。

注意

> 你不能仅仅通过观察图像来确定什么是固定的，什么是变化的。你还必须仔细阅读问题陈述，并深入思考。

从我们的描述中可以清楚地看出，有两件事情在变化：飞机的位置和剩余燃料的数量。因此，世界状态必须捕捉这两者的当前值。燃料最好表示为一个单一的数字。然而，我们确实需要创建一个新的结构来表示这两者的组合。

世界定义

> 世界状态是一个表示飞机当前位置和剩余燃料量的结构。

具体来说，我们将使用这个结构：

```
data World:
  | world(p, f)
end
```

> 练习
> 
> > 我们也可以将世界定义为由三个组件组成的结构：飞机的 x 位置，飞机的 y 位置和燃料的数量。为什么我们选择使用上面的表示形式？

我们可以再次查看程序的每个部分，以确定什么可以保持不变，什么需要改变。具体来说，我们必须关注消耗和产生世界的函数。

在每个滴答声中，我们消耗一个世界并计算一个世界。时间的流逝不消耗任何燃料，因此这段代码可以保持不变，除了必须创建一个包含当前燃料量的结构之外。具体来说：

```
fun move-airplane-xy-on-tick(w :: World):
  world(
    posn(
      move-airplane-wrapping-x-on-tick(w.p.x),
      move-airplane-y-on-tick(w.p.y)),
    w.f)
end
```

类似地，响应按键的功能明显需要考虑剩余燃料的多少：

```
fun alter-airplane-y-on-key(w, key):
  ask:
    | key == "up"   then:
      if w.f > 0:
        world(posn(w.p.x, w.p.y - KEY-DISTANCE), w.f - 1)
      else:
        w # there's no fuel, so ignore the keystroke
      end
    | key == "down" then:
      world(posn(w.p.x, w.p.y + KEY-DISTANCE), w.f)
    | otherwise: w
  end
end
```

> 练习
> 
> > 更新渲染场景的函数。请记住，世界有两个字段；其中一个对应于我们以前绘制的内容，而另一个不会在输出中显示。
> > 
> 练习
> 
> > 扩展你的程序以绘制燃料表。

## 11.10 版本：气球也移动了。

到目前为止，我们的气球一直是静止的。让我们通过让气球移动来使游戏更加有趣，正如这个视频所示：

[`world.cs.brown.edu/1/projects/flight-lander/v8.swf`](http://world.cs.brown.edu/1/projects/flight-lander/v8.swf)

显然，气球的位置也需要成为世界状态的一部分。

世界定义

> 世界状态是一个表示飞机当前位置、气球当前位置和剩余燃料量的结构。

这是世界状态的表示：

```
data World:
  | world(p :: Posn, b :: Posn, f :: Number)
end
```

根据这个定义，我们显然需要重新编写我们所有以前的定义。相对于我们之前看到的内容，这大部分是相当例行的。我们真正没有详细说明的唯一细节是气球应该如何移动：向什么方向、以多快的速度以及在边缘时该怎么做。我们将让你自己想象一下！（记住，气球越靠近陆地，安全着陆飞机就越困难。）因此，我们必须修改：

+   背景图像（去除静态气球）。

+   绘制处理程序（用于在其位置绘制气球）。

+   定时处理程序（移动气球以及飞机）。

+   关键处理程序（构造使气球保持不变的世界数据）。

+   终止条件（考虑到气球的动态位置）。

> 练习
> 
> > 修改上述每个函数及其测试用例。

## 11.11 版本：一个，两个，……，九十九个彩色气球！

最后，我们没有必要限制自己只有一个气球。多少个合适？两个？三个？十个？……为什么要固定任何一个数字？它可以是一个气球节日！[](../Images/b215747783cfd450a745d171bb0bb796.jpg)

阿尔伯克基气球节

同样，许多游戏有逐渐变难的关卡；我们也可以这样做，让气球数量成为跨级别变化的一部分。然而，拥有两个气球和五个气球在概念上没有太大区别；控制每个气球的代码本质上是相同的。

我们需要表示一系列气球。我们可以使用列表来表示它们。因此：

世界定义

> 世界状态是一个表示飞机当前位置、气球位置列表和剩余燃料数量的结构。

现在你应该使用结构列表的设计方案重写这些函数。注意，你已经编写了移动一个气球的函数。还剩下什么？

1.  对列表中的每个气球应用相同的函数。

1.  确定两个气球碰撞时该怎么办。

目前，你可以通过沿 x 维度充分分开放置每个气球并让它们只能上下移动来避免后一个问题。

> 练习
> 
> > 引入风的概念，它影响气球但不影响飞机。在随机时间段后，风以随机速度和方向吹动，导致气球横向移动。
