# 第一部分: 技巧

+   1\. 快速开始

    +   安装

    +   踏出第一步

    +   总结

+   2\. 配置

    +   单一配置

    +   多配置

    +   说明

+   3\. 项目结构

    +   普通的项目结构

    +   项目结构具体说明

    +   说明

+   4\. 展示一个页面

    +   路由和视图函数

    +   蓝图

    +   说明

+   5\. 数据库使用

    +   操作 Mysql

    +   操作 MongoDB

    +   操作 Redis

    +   说明

+   6\. 常用的技巧

    +   验证问题

    +   gRPC 的异步调用方式

    +   Blueprint

    +   html&templates 编写

    +   cache

    +   热加载

    +   session

+   7\. 可靠的扩展

+   8\. 测试与部署

    +   测试

    +   部署

+   9\. 说明

+   10\. 第一部分: 技巧

# 快速开始

在安装 Sanic 之前，让我们一起来看看 Python 在支持异步的过程中，都经历了哪些比较重大的更新。

首先是 Python3.4 版本引入了`asyncio`，这让 Python 有了支持异步 IO 的标准库，而后 3.5 版本又提供了两个新的关键字`async/await`，目的是为了更好地标识异步 IO，让异步编程看起来更加友好，最后 3.6 版本更进一步，推出了稳定版的`asyncio`，从这一系列的更新可以看出，Python 社区正迈着坚定且稳重的步伐向异步编程靠近。

## 安装

Sanic 是一个支持 `async/await` 语法的异步无阻塞框架，这意味着我们可以依靠其处理异步请求的新特性来提升服务性能，如果你有`Flask`框架的使用经验，那么你可以迅速地使用`Sanic`来构建出心中想要的应用，并且性能会提升不少，我将同一服务分别用 Flask 和 Sanic 编写，再将压测的结果进行对比，发现 Sanic 编写的服务大概是`Falsk`的 1.5 倍。

仅仅是 Sanic 的异步特性就让它的速度得到这么大的提升么？是的，但这个答案并不标准，更为关键的是 Sanic 使用了`uvloop`作为`asyncio`的事件循环，`uvloop`由 Cython 编写，它的出现让`asyncio`更快，快到什么程度？[这篇](http://codingpy.com/article/uvloop-blazing-fast-networking-with-python/) [http://codingpy.com/article/uvloop-blazing-fast-networking-with-python/]文章中有介绍，其中提出速度至少比 nodejs、gevent 和其他 Python 异步框架要快两倍，并且性能接近于用 Go 编写的程序，顺便一提，Sanic 的作者就是受这篇文章影响，这才有了 Sanic。

怎么样？有没有激起你学习 Sanic 的兴趣，如果有，就让我们一起开始学习吧，在开始之前，你只需要有一台安装了 Python 的电脑即可。

> 说明：由于 Windows 下暂不支持安装 uvloop，故在此建议使用 Mac 或 Linux

### 虚拟环境

程序世界一部分是对应着现实的，在生活中，我们会在不同的环境完成不同的任务，比如在厨房做饭、卧室休息，分工极其明确。

其实用 Python 编写应用服务也是如此，它们同样希望应用服务与开发环境是一对一的关系，这样做的好处在于，每个独立的环境都可以简洁高效地管理自身对应服务所依赖的第三方库，如若不然，各个服务都安排在同一环境，这样不仅会造成管理上的麻烦，还会使第三方库之间产生冲突。

通过上面的叙述，我们是不是可以得出这样一个核心观点：**应该在不同的环境下做不同的事** ，以此类推，写项目的时候，我们也需要为每个不同的项目构建一个无干扰的的环境，发散思维，总结一下：

> 不同的项目，需要为其构建不同的虚拟环境，以免互相干扰

构建虚拟环境的工具很多，如下：

+   [virtualenv](https://virtualenv.pypa.io/en/stable/) [https://virtualenv.pypa.io/en/stable/]

+   [pyenv](https://github.com/pyenv/pyenv) [https://github.com/pyenv/pyenv]

+   [anaconda](https://www.continuum.io/downloads) [https://www.continuum.io/downloads]

…...

以上三个工具都可以快速地帮助我们构建当前需要的 Python 环境，如果你之前没有使用过，可直接点开链接进行下载，如果你正在使用其它的环境管理工具，也不要紧，因为不论你使用哪一种方式，我们最终目的都是针对一个新项目构建一个新的环境。

安装配置好之后，简单看看官方提供的使用方法，就可以开始了，比如我本机使用的是`anaconda` ，安装完成后可以很方便地创建一个虚拟环境，比如这里使用 Python3.6 来作为本书项目的默认环境：

```
# 新建一个 python3.6 环境
conda create --name python36 python=3.6
# 安装好之后 输入下面命令进入名为 python36 的环境
source activate python36 
```

若安装速度比较慢，可以考虑换国内源，比如 [国内镜像](https://mirrors.tuna.tsinghua.edu.cn/help/pypi/) [https://mirrors.tuna.tsinghua.edu.cn/help/pypi/] ，至于为什么选择 python3.6 作为默认环境，一是因为 Sanic 只支持 Python3.5+，二则是我们构建的项目最终是要在生产环境下运行的，所以建议最好安装 Python3.6 下稳定版本的`asyncio`。  ### 安装 Sanic

Python 安装第三方模块都是利用`pip`工具进行安装，这里也不例外，首先进入上一步我们新建的 `python3.6` 虚拟环境，然后安装：

```
# 安装 Sanic，请先使用 source activate python36 进入虚拟环境
pip install sanic
# 如果不想使用 uvloop 和 ujson 可以这样安装
SANIC_NO_UVLOOP=true SANIC_NO_UJSON=true pip install sanic 
```

通过上面的命令，你就可以在 `python3.6` 虚拟环境中安装 Sanic 以及其依赖的第三方库了，若想查看 Sanic 是否已经正确安装，可以进入终端下对应的虚拟环境，启动 Python 解释器，导入 Sanic 库：

```
# 启动 Python 解释器
python
>>> import sanic
>>> 
```

如果没有出现错误，就说明你已经正确地安装了 Sanic，请继续阅读下一节，了解下如何利用 Sanic 来构建一个 Web 项目吧。  ## 踏出第一步

我们将正式使用 Sanic 来构建一个 web 项目，让我们踏出第一步，利用 Sanic 来编写一个返回`Hello World!`字符串的服务程序。

新建一个文件，名为 `run.py` :

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import text

app = Sanic()

@app.route("/")
async def test(request):
    return text('Hello World!')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

Sanic 的目标是��编写服务更加简单易用，请看上面仅用不到 10 行的代码，就编写好了一个简单的 Web 服务，运行此文件，在浏览器输入 `http://0.0.0.0:8000` ，出现的字符会让你回想起当年学 c 的恐惧^_^。

如果你是第一次使用 Sanic，上面的代码可能会让你产生一些困扰，不用担心，接下来，我们将一起用 Sanic 编写一个简单的资讯阅读的 web 服务，在这过程中，你将逐渐地了解到 Sanic 的一些基本用法，如路由的构建、接受请求数据以及返回响应的内容等。

本次示例的源代码全部在 github 上，见[examples/demo01/news.py](https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/examples/demo01/news.py) [https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/examples/demo01/news.py]。

### 编写一个资讯阅读项目

在开始编写之前，第一步最好写一下需求，哪怕是个简单不过的玩具项目也不能略过这个步骤，比如现在编写的资讯阅读项目，需求就一个，在页面中展示一些资讯新闻。

既然是展示资讯新闻，那么解决数据来源的问题最为重要，对于这个问题你也不用担心，因为在本次示例的源码中我编写了一个名为`get_news()`的函数专门用来返回资讯新闻数据，简化代码如下:

```
async def get_news(size=10):
    """
 Sanic 是一个异步框架，为了更好的发挥它的性能，有些操作最好也要用异步的
 比如这里发起请求就必须要用异步请求框架 aiohttp
 所以使用本服务的时候请先执行: pip install aiohttp
 数据使用的是 readhub 网站的 api 接口
 为了使这个数据获取函数正常运行，我会保持更新，所以具体代码：examples/demo01/news.py
 """
    async with aiohttp.ClientSession() as client:
        async with client.get(readhub_api, params=params, headers=headers) as response:
            assert response.status == 200
            text = await response.json()
        return text 
```

这样各位就可以只专注于 Sanic 的代码实现，而不必考虑其他问题，我会一直维护这个数据获取函数，以保证数据正常输出，各位请放心使用。  ### 构建路由

数据的问题解决之后，我们可以开始着手于需求的实现了，根据前面的描述，此时的需求是当客户端（Web 浏览器）访问`http://0.0.0.0:8000/`的时���，浏览器会立马展示服务端响应返回的 10 条资讯新闻（假设内容由 index()函数返回），若浏览器访问的是`http://0.0.0.0:8000/2`，此时返回的就是第二页的 10 条资讯新闻，以此类推......

当 Sanic 程序实例接收到一个请求，比如前面提到的`http://0.0.0.0:8000/`，它是怎么知道这个 URL 可以对应到`index()`函数呢？

Sanic 有一个机制来保存 URL 和函数（一般称之为视图函数）之间的映射关系，就像`dict`中`key`和`value`，这样当服务端接收到请求`http://0.0.0.0:8000/`，就会立马知道，接下来需要调用`index()`函数了，我们将其称之为路由。

Sanic 中可以用`app.route`修饰器来定义路由，当 Sanic 服务启动的时候，`app.route`就会将其中传入的参数与装饰的函数自动注册好，比如下面这段代码：

```
@app.route("/")
async def index(request):
    """当服务端接收到客户端的/请求时，就会调用此函数"""
    return text('Hello World!') 
```

此时请求`http://0.0.0.0:8000/`就会返回`Hello World!`，很显然，这不是我们想要的需求，我们的需求是展示 10 条资讯新闻，数据怎么来？你只需要调用`get_news()`函数，就会获取到你想要的资讯数据：

```
@app.route("/")
async def index(request):
    # html 页面模板
    html_tem = """
 <div style="width: 80%; margin-left: 10%">
 <p><a href="{href}" target="_blank">{title}</a></p>
 <p>{summary}</p>
 <p>{updated_at}</p>
 </div>
 """
    html_list = []
    # 获取数据
    all_news = await get_news()
    # 生成在浏览器展示的 html 页面
    for each_news in all_news:
        html_list.append(html_tem.format(
            href=each_news.get('news_info', [{}])[0].get('url', '#'),
            title=each_news.get('title'),
            summary=each_news.get('summary'),
            updated_at=each_news.get('updated_at'),
        ))

    return html('<hr>'.join(html_list)) 
```

运行此服务：

```
python run news.py 
```

此时，访问`http://0.0.0.0:8000/`，你就会获得 Sanic 服务程序返回的资讯新闻，如下图，可以看到返回服务端提供的最新资讯：

![01_0](img/01_0.jpg)

页面成功地呈现出我们想要的结果，实在是令人兴奋，等等，不能高兴太早，我们还有一个需求，要根据浏览器输入的页数来展示内容，如：`http://0.0.0.0:8000/2`，思考一下，应该怎样优雅地完成这个需求，或许你会想，再构建一对 URL 与视图函数的映射关系，像下面这样：

```
@app.route("/2")
async def page_2(request): 
```

不得不说，这是一个糟糕的解决方案，这样没法解决接下来的第 3 页、第 4 页、甚至第 n 页（虽然目前这个服务程序只展示到第 2 页），最佳实践应该是把页数当做变量来获取，Sanic 的路由机制自然提供了获取动态请求参数的功能，如下：

```
@app.route("/<page:int>")
@app.route("/")
async def index(request, page=1):
    """
 支持/请求与/page 请求方式
 具体的代码逻辑也会有一点改变，可参考：examples/demo01/news.py
 """ 
```

再次运行此服务：

```
python run news.py 
```

不论是请求`http://0.0.0.0:8000/`或者`http://0.0.0.0:8000/2`，都是我们想要的结果。  ### 请求数据

细心的你可能会发现，每次编写一个视图函数的时候，总是有一个`request`参数：

```
async def index(request, page=1): 
```

为什么必须定义这个参数，它从哪来？它有什么作用，下面我将一一为你解答。

如果你在客户端请求`http://0.0.0.0:8000/`的时候，顺手在视图函数里面打印下参数`request`，会有如下输出：

```
<Request: GET /> 
```

看终端的输出可以了解到`request`参数实际上是一个名为`Request`的实例对象，每当服务端接收到一个请求，Sanic 的`handle_request`函数必定会接收一个`Request`实例对象，这个实例对象包含了一系列请求信息。

前面说到，每个 URL 对应一个视图函数，而 Sanic 的`handle_request`接下来会将接收的`Request`实例对象作为参数传给 URL 对应的视图函数，也就是上面`index`的`request`参数，这样一来，就必须定义`request`来接收`Request`实例对象，其中包含的一些请求信息对视图函数来说非常重要，目前`Request`对象提供了以下属性：

+   json

+   token

+   form

+   files

+   args

+   raw_args

+   cookies

+   ip

+   port

+   socket

+   remote_addr

+   path

+   url

上面只是列出了一部分属性，如果你想了解更多，可查看[request.py](https://github.com/channelcat/sanic/blob/master/sanic/request.py) [https://github.com/channelcat/sanic/blob/master/sanic/request.py]源码文件了解。

为了可以实际使用下`request`，我们可以再加一个需求，比如增加一个`GET`请求的接口`http://0.0.0.0:8000/json`，如果请求不设置参数`nums`的值，则默认返回一条资讯新闻，如果设置了`nums`参数，则该接口返回的新闻数量由参数值决定，参数最大值为 10：

```
@app.route('/json')
async def index_json(request):
    """
    默认返回一条资讯，最多十条
    """
    nums = request.args.get('nums', 1)
    # 获取数据
    all_news = await get_news()
    try:
        return json(random.sample(all_news, int(nums)))
    except ValueError:
        return json(all_news) 
```

运行此服务：

```
python run news.py 
```

此时视图函数`index_json`就可以根据接受的参数`nums`来返回对应数量的新闻，访问`http://0.0.0.0:8000/json?nums=2`，效果如下：

![01_1](img/01_1.jpg)  ### 响应

不论哪个 Web 框架，都是需要构建响应对象的，Sanic 自然也不例外，它用的是`sanic.response`来构建响应对象，像上面的代码中可以看到：

```
from sanic.response import html, json 
```

这表示我们目前构建的资讯阅读服务，分别返回了`body`格式为`html`以及`json`的响应对象，除了这两种格式，Sanic 还提供了下面几种格式：

+   json

+   text

+   raw

+   html

+   file

+   file_stream

+   stream

更多属性请看[response.py](https://github.com/channelcat/sanic/blob/master/sanic/response.py) [https://github.com/channelcat/sanic/blob/master/sanic/response.py]，我们可以根据实际需求来构建响应对象，最后再返回给客户端。  ### 继续深入

不要以为现在编写的资讯服务已经很完善了，其实还有许多问题需要我们解决，比如访问`http://0.0.0.0:8000/html`这个 URL 会返回：

```
Error: Requested URL /html not found 
```

服务程序为什么会抛出这个错误？因为程序中并路由没有注册`html`，并且没有进行错误捕捉（比如此时的 404），解决这个问题也很方便，比如把这个错误全部跳转到首页，代码如下：

```
@app.exception(NotFound)
def ignore_404s(request, exception):
    return redirect('/') 
```

此时访问一些没有注册于路由的 URL，比如此时的`http://0.0.0.0:8000/html`都会自动跳转到`http://0.0.0.0:8000/`。

现在，我们已经用 Sanic 编写了一个简单的资讯阅读服务，在编写的过程中使用了路由、数据请求、处理以及响应对象，这些基础知识足够你编写一些基���的服务，但这还远远不够，比如模板引、引入静态文件等，这些都等着我们在实践中继续深入了解。  ## 总结

本章介绍了 Sanic 的安装以及基本的使用，目标是希望诸位可以迅速的了解并掌握 Sanic 的基本使用方法，并为阅读接下来的章节打一下基础。

文档以及代码：

+   `Sanic` github 地址：[`github.com/channelcat/sanic`](https://github.com/channelcat/sanic)

+   官方教程：[`sanic.readthedocs.io/en/latest/`](http://sanic.readthedocs.io/en/latest/)

+   demo 地址：[demo01](https://github.com/howie6879/Sanic-For-Pythoner/blob/master/examples/demo01/run.py) [https://github.com/howie6879/Sanic-For-Pythoner/blob/master/examples/demo01/run.py]  # 配置

对于一个项目来说，配置是一个很严肃的问题，比如说：在开发环境和生产环境中，配置是不同的，那么一个项目该如何自由地在不同的配置环境中进行切换呢，思考下，然后带着答案或者疑问往下阅读。

## 单一配置

撸起袖子，开始吧，新建文件夹 `demo2` ，内部建立这样的文件结构：

```
demo02
├── config
│   ├── __init__.py
│   └── config.py
└── run.py 
```

其中 `run.py` 内容如下：

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import text

app = Sanic()

@app.route("/")
async def test(request):
    return text('Hello World!')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000, debug=True) 
```

代码示例中开启了 `debug` 模式，假设我们需要通过 `config.py` 配置文件来实现控制服务的 `debug` 模式开启与否，那该怎么实现呢。

在 `config.py` 中添加一行：`DEBUG=True` ，然后 `run.py` 内容��为：

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import text
from config import DEBUG

app = Sanic()

@app.route("/")
async def test(request):
    return text('Hello World!')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000, debug=DEBUG) 
```

表面上看，功能确实实现了，但这实际上却不是很好的做法，若部署在生产环境中，难道还要特地再将 `debug` 改为 `False` 么，这显然很浪费时间，如果需要改变的参数有很多，那就很难维护了。  ## 多配置

那么，正确的做法应该是怎么样的呢？

我们应当依据不同的环境来编写各自对应的环境，举个例子，比如生产环境就对应`pro_config`，开发环境就对应`dev_config.py`等等

具体该怎么实施？首先在文件夹 `demo2` ，内部建立这样的文件结构：

```
demo02
├── config
│   ├── __init__.py
│   ├── config.py
│   ├── dev_config.py
│   └── pro_config.py
└── run.py 
```

然后使用类继承的方式使这三个配置文件联系起来，比如在 `config.py` 中就只放公有配置，如：

```
#!/usr/bin/env python
import os

class Config():
    """
 Basic config for demo02
 """
    # Application config
    TIMEZONE = 'Asia/Shanghai'
    BASE_DIR = os.path.dirname(os.path.dirname(__file__)) 
```

而在 `pro_config.py 或 dev_config.py` 中就可以自由地编写不同的配置了：

```
# dev_config
#!/usr/bin/env python
from .config import Config

class DevConfig(Config):
    """
 Dev config for demo02
 """

    # Application config
    DEBUG = True

# pro_config
#!/usr/bin/env python
from .config import Config

class ProConfig(Config):
    """
 Pro config for demo02
 """

    # Application config
    DEBUG = False 
```

配置文件还需要根据系统环境变量的设置进行不同配置环境的切换，比如设置 `MODE` 系统环境变量，这里从系统环境变量得到配置也是个不错的方法，一般说利用`gunicorn`配置`worker`数目之类的，都可以使用这种方案。

然后可以根据其不同的值切换到不同的配置文件，因此在 `__init__.py` 中需要这么写：

```
#!/usr/bin/env python
import os

def load_config():
    """
 Load a config class
 """

    mode = os.environ.get('MODE', 'DEV')
    try:
        if mode == 'PRO':
            from .pro_config import ProConfig
            return ProConfig
        elif mode == 'DEV':
            from .dev_config import DevConfig
            return DevConfig
        else:
            from .dev_config import DevConfig
            return DevConfig
    except ImportError:
        from .config import Config
        return Config

CONFIG = load_config() 
```

默认 `MODE` 设置为 `DEV`，在 `run.py` 文件中就可以这么调用：

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import text
from config import CONFIG

app = Sanic()
app.config.from_object(CONFIG)

@app.route("/")
async def test(request):
    return text('Hello World!')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000, debug=app.config['DEBUG']) 
```

而在生产环境的服务器上，直接通过设置系统变量就可以达到配置修改的目的了，如下：

```
# 通过设置 MODE 的值进行配置文件的选择
export MODE=PRO 
```

若是利用 `supervisor` 来启动服务，可通过添加`environment = MODE="PRO"` 来设置环境变量，是不是很方便呢。  ## 说明

其实我编写这种微服务，配置更新是很正常且很频繁的需求，这样的话我就必须要求我的代码可以实现热更新，也就是可以迅速的修改配置，且迅速的生效，目前我使用的是`ZooKeeper`来实现这个需求，有兴趣的朋友可以详细了解，或许你也是用这个方案呢？

如果你有更好的方案，不妨告知一二。  # 项目结构

通过前面的讲解，我们了解了`Sanic`的运行方式以及编写一个好的配置方案，是不是想要立马编写一个应用练练手呢？别急，请先看完这一章节，了解一下你要写的应用得用什么样的结构。

在`github`上也看了不少的`Python`项目吧，相信你也清楚，一个项目，在最外层他们应该是一样的，简单概括下，大概是下面这样的结构:

```
pro_name
├── docs            # 项目文档说明
├── src or pro_name/# 项目名称
├── tests           # 测试用例
├── README.md       # 项目介绍
└──requirements.txt # 该项目依赖的第三方库 
```

那接下来需要讨论的，就是 `src` 或者说`pro_name`（这个就看你心情命名了，一般与最外层一样的名字）的内部结构该是什么样的呢？

本章将写一个 `rss` 解析展示的项目用做演示。

## 普通的项目结构

一个普通的项目：

+   不需要添加后续模块功能

+   快速开发使用，不需要维护

+   无较复杂的前端需求

+   用完就走

那么就可以像 `demo01` 中一样，只需要添加一个 [run.py](https://github.com/howie6879/Sanic-For-Pythoner/blob/master/examples/demo03/sample01/src/run.py) [https://github.com/howie6879/Sanic-For-Pythoner/blob/master/examples/demo03/sample01/src/run.py] 或者叫做 `app.py` 文件（反正这是一个启动文件，命名可随意），不论是配置、路由都写在一起就好了。

新建一个项目如下：

```
sample01
├── docs
│   └── demo.md
├── src
│   └── run.py
├── tests
├── .gitignore
└──requirements.txt 
```

任意一个 `rss` 源，假设项目需要将其中的文章标题以及链接提取并展示出来，比如以 json 格式返回，这属于很简单的功能，可以说只有一段逻辑，`run.py` 内容如下：

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import json
from feedparser import parse

app = Sanic()

@app.route("/")
async def index(request):
    url = "http://blog.howie6879.cn/atom.xml"
    feed = parse(url)
    articles = feed['entries']
    data = []
    for article in articles:
        data.append({"title": article["title_detail"]["value"], "link": article["link"]})
    return json(data)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

访问 `http://0.0.0.0:8000/`，会返回一串 json，如下：

![rss-json](img/03-01.png)

和我们想象地一样，返回了一串`json`，接下来，问题升级，我想要将标题链接用页面展示，该怎么弄？

很容易想到，我们需要一个页面模板来承载数据，然后将 json 数据写入到页面模板中，最后用 `jinja2` 的 `template` 将其渲染。

道理我们都懂，`Sanic`具体需要怎么渲染呢？说白了就是对`jinja2`的使用，如下：

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import json, text, html
from feedparser import parse
from jinja2 import Template

app = Sanic()

# 后面会使用更方便的模板引用方式
template = Template(
    """
 <!DOCTYPE html>
<html lang="en">
<head>
 <meta charset="UTF-8">
 <title>rss 阅读</title>
 <meta name="viewport" content="width=device-width, initial-scale=1">
</head>
<body>
<article class="markdown-body">
 {% for article in articles %}
 <b><a href="{{article.link}}">{{article.title}}</a></b><br/>
 <i>{{article.published}}</i><br/>
 <hr/>
 {% endfor %}
</article>
</body>
</html>
 """
)

@app.route("/")
async def index(request):
    url = "http://blog.howie6879.cn/atom.xml"
    feed = parse(url)
    articles = feed['entries']
    data = []
    for article in articles:
        data.append({"title": article["title_detail"]["value"], "link": article["link"]})
    return json(data)

@app.route("/html")
async def rss_html(request):
    url = "http://blog.howie6879.cn/atom.xml"
    feed = parse(url)
    articles = feed['entries']
    data = []
    for article in articles:
        data.append(
            {"title": article["title_detail"]["value"], "link": article["link"], "published": article["published"]})
    html_content = template.render(articles=data)
    return html(html_content)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

具体结构代码见[sample01](https://github.com/howie6879/Sanic-For-Pythoner/tree/master/examples/demo03/sample01) [https://github.com/howie6879/Sanic-For-Pythoner/tree/master/examples/demo03/sample01]，运行起来，然后输入 `http://0.0.0.0:8000/html` 就可以看到被展示出来的页面^_^

![rss-html](img/03-02.png)

假设需要编写前端页面比较多，那么你就需要添加`statics` 以及 `templates` 文件夹用来管理各个界面模块，具体下面会介绍。  ## 项目结构具体说明

当编写的项目过于复杂，我都会将其当做一个第三方包来管理项目中涉及的各种模块，比如 [sample02](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/sample02) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/sample02]，目录下面你会发现有个 `__init__.py` 文件，它初始化了当前目录下的应用，然后代码中引用某个函数可以这么写：

```
from src.views import app 
```

这样，你的应用下面的模块引用起来就会特别方便，就像使用一个第三方模块一样，灵巧且方便。

每个项目的内部分布以及命名可能不一样（甚至目录比应该或多或少），但大体意思可能差不多，下面介绍本次项目 `src` 下的一些文件目录结构：

```
sample02
├── docs
│   └── demo.md
├── src
│   ├── config # 配置 
│   ├── statics # css、js、img
│   ├── templates # Jinja2 模板
│   └── views # 路由、逻辑处理
│   ├── __init__.py
│   ├── run.py # 启动文件
├── tests
└── requirements.txt 
```

此处就可以将 `sample02` 当成一个包了，实践是检验真理的唯一标准，让我们来试试看：

首先新建文件 `/views/rss.py` ，具体代码可以看这里 [sample02](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/sample02) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/sample02]，下面��代码片段可没办法很好的运行:

```
enable_async = sys.version_info >= (3, 6)

app = Sanic()

# jinjia2 config
env = Environment(
    loader=PackageLoader('views.rss', '../templates'),
    autoescape=select_autoescape(['html', 'xml', 'tpl']),
    enable_async=enable_async)

async def template(tpl, **kwargs):
    template = env.get_template(tpl)
    rendered_template = await template.render_async(**kwargs)
    return html(rendered_template)

@app.route("/html")
async def rss_html(request):
    url = "http://blog.howie6879.cn/atom.xml"
    feed = parse(url)
    articles = feed['entries']
    data = []
    for article in articles:
        data.append(
            {"title": article["title_detail"]["value"], "link": article["link"], "published": article["published"]})
    return await template('rss.html', articles=articles) 
```

这里使用异步的方式引入了 `jinja2` ，需要注意的是 python 版本必须 3.6+，否则就得使用同步的方式来引入 `jinja2` ，后面章节会继续介绍。

此时启动文件 `run.py` 只要引入 `/views/rss.py` 的 `app` 实例即可：

```
# !/usr/bin/env python
import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.views import app
from src.config import CONFIG

app.statics('/statics', CONFIG.BASE_DIR + '/statics')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

还有一些 css 文件这里就不介绍，具体代码请看[sample02](https://github.com/howie6879/Sanic-For-Pythoner/tree/master/examples/demo03/sample02) [https://github.com/howie6879/Sanic-For-Pythoner/tree/master/examples/demo03/sample02]，运行起来，然后输入 `http://0.0.0.0:8000/html` 就好，效果如下图：

![rss-html](img/03-03.png)  ## 说明

关于 `views templates statics` 内部的构造也是值得一写，这就涉及到蓝图 `Blueprint` ，后面介绍蓝图的时候会进行介绍。

代码地址：[demo03](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo03/]  # 展示一个页面

前面一章介绍[项目结构](https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part1/3.%E9%A1%B9%E7%9B%AE%E7%BB%93%E6%9E%84.md) [https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part1/3.%E9%A1%B9%E7%9B%AE%E7%BB%93%E6%9E%84.md]的时候，很粗略地讲了下如何将 rss 的文章内容在网页上进行展示。

相信你应该已经了解清楚，`sanic`是怎么接收请求并返回被请求的资源的，简单来说概括如下：

+   接收请求

+   找到对应的路由并执行路由对应的视图函数

+   [Jinja2](http://jinja.pocoo.org/docs/2.10/) [http://jinja.pocoo.org/docs/2.10/]模板渲染返回视图

## 路由和视图函数

在此我假设你理解 `python` 中的装饰器，如果你并不清楚，可以看我另写的关于[装饰器](http://blog.howie6879.cn/2016/09/28/04/) [http://blog.howie6879.cn/2016/09/28/04/]的介绍，回归正题，还记得第一节中的代码实例么？

```
#!/usr/bin/env python
from sanic import Sanic
from sanic.response import text

app = Sanic()

# 此处将路由 / 与视图函数 test 关联起来
@app.route("/")
async def test(request):
    return text('Hello World!')

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

在前言介绍里，出现这几个名词 **路由 视图函数 视图** ,在上面那段代码中，`test` 就是视图函数。

这是一段执行逻辑，比如客户端请求 `0.0.0.0:8000/` 此时返回的内容就是由`test` 这个视图函数提供的。

在我看来，视图函数就是一个纽带，它起到承上启下的作用，那么，到底是怎样的承上启下呢？让我们结合代码([sanic0.1.2 源码](https://github.com/howie6879/Sanic-For-Pythoner/blob/master/docs/part2/1.Sanic%E6%BA%90%E7%A0%81%E9%98%85%E8%AF»-基于 0.1.2.md) [https://github.com/howie6879/Sanic-For-Pythoner/blob/master/docs/part2/1.Sanic%E6%BA%90%E7%A0%81%E9 阅读-基于 0.1.2.md])来分析下：

```
 @app.route("/")
async def test(request):
    return text('Hello World!') 
```

这个路由装饰器的作用很简单，就是将 `/` 这个 `uri` 与视图函数`test`关联起来，或许你可以将路由想象成一个 `dict`，当客户端若请求 `0.0.0.0:8000/`，路由就会`get` `/` 对应的视图函数`test`，然后执行。

其实真实情况和我们想象的差不多，请看 `sanic.py` 中的第三十行:

```
 # Decorator
def route(self, uri, methods=None):

    def response(handler):
        # 路由类的 add 方法将视图函数 handler 与 uri 关联起来
        # 然后整个路由列表会新增一个 namedtuple 如下：
        # Route(handler=handler, methods=methods_dict, pattern=pattern, parameters=parameters)
        self.router.add(uri=uri, methods=methods, handler=handler)
        return handler

    return response 
```

此时，路由就和 `uri` 对应的视图函数关联起来了，这就是承上，路由和视图函数就是这样对应的关系。 103 行有个`handle_request`函数：

```
 async def handle_request(self, request, response_callback):
    """
 Takes a request from the HTTP Server and returns a response object to be sent back
 The HTTP Server only expects a response object, so exception handling must be done here
 :param request: HTTP Request object
 :param response_callback: Response function to be called with the response as the only argument
 :return: Nothing
 """ 
```

当服务器监听到某个请求的时候，`handle_request`可以通过参数中的`request.url` 来找到视图函数并且执行，随即生成视图返回，这便是所谓的启下。

其实浏览器显示的内容就是我们所谓的视图，视图是视图函数生成的，其中 Jinja2 起到模板渲染的作用。  ## 蓝图

到这里，你一定已经很明白 sanic 框架是怎么处理一个请求并将视图返回给客户端，然后也掌握了如何编写自己定义的模板(html)以及样式(css)，通过前面一节[项目结构](https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part1/3.项目结构.md) [https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part1/3.项目结构.md]的介绍，我们可以总结出如下经验：

+   对于 css、js 等静态文件，常规操作是将其放在自己建立的 statics 下面

+   对于 html 模板，常规操作是将其放在自己建立的 templates 下面

+   视图函数(即服务的逻辑实现)放在自己建立的 views 下面

是时候考虑以下这种情况了，你需要编写一个比较复杂的 http 服务，你需要定义几百个路由，��编写过程中你会发现有许多不顺心的地方：

+   各种不同类型的路由互相交杂在一起，命名困难，管理困难

+   不同页面的 css 文件同样堆积在一起，html 也是如此

+   ...

实在是令人烦恼，可能你想要一个模块化的编写方式，一个文件编写后台，url 统一是`/admin/***`，一个文件编写发帖，`/post/***` 等等，各个文件下面 url 自动会带上自定义的前缀，不用考虑命名问题，不用重复写 url 前缀，多么美好

**Blueprint**，就是 sanic 为你提供的解决方案，依然是上节 rss 的例子，让我们利用 Blueprint 来简单实现一下我们的需求，比如我们要构建的网站分为两个部分：

+   `/json/index` 返回 json 格式的数据

+   `/html/index` 返回 html 视图

我们在上节代码的基础上添加 Blueprint，先看看定好的项目结构[demo04](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/]，和前面相比，现在的项目结构是不是感觉很丰富？继续往下看：

```
.
├── __init__.py
├── config
│   ├── __init__.py
│   ├── config.py
│   ├── dev_config.py
│   └── pro_config.py
├── run.py
├── statics
│   ├── rss_html # rss_html 蓝图的 css js 文件存放目录
│   │   ├── css
│   │   │   └── main.css
│   │   └── js
│   │   │   └── main.js
│   └── rss_json # rss_json 蓝图的 css js 文件存放目录
│   │   ├── css
│   │   │   └── main.css
│   │   └── js
│   │   │   └── main.js
├── templates
│   ├── rss_html # rss_html 蓝图的 html 文件存放目录
│   │   ├── index.html
│   │   └── rss.html
│   └── rss_json # rss_json 蓝图的 html 文件存放目录
│       └── index.html
└── views
    ├── __init__.py
    ├── rss_html.py # rss_html 蓝图
    └── rss_json.py # rss_json 蓝图 
```

蓝图的目的就是让我们构建的项目灵活，可扩展，容易阅读，方便管理，一个个小的蓝图就构建了一个大型的项目，run.py 里面可以随意组合注册蓝图，可抽插式的构建我们的服务，[sample01](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/sample01) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/sample01]里是本次示例的代码，建议先读一遍，十分简单，主要就是讲路由根据你自己定义的特性分割成一个个蓝图，比如这里的`rss_html`和`rss_json`，请特别注意项目中对于静态文件以及模板文件的路径配置:

```
 #!/usr/bin/env python
# 部分代码
# rss_html.py
import sys

from sanic import Blueprint
from sanic.response import html

from src.config import CONFIG

html_bp = Blueprint('rss_html', url_prefix='html')
html_bp.static('/statics/rss_html', CONFIG.BASE_DIR + '/statics/rss_html')

# jinjia2 config
env = Environment(
    loader=PackageLoader('views.rss_html', '../templates/rss_html'),
    autoescape=select_autoescape(['html', 'xml', 'tpl']),
    enable_async=enable_async)

@html_bp.route("/")
async def index(request):
    return await template('index.html')

#!/usr/bin/env python
# 部分代码
# rss_json.py
import sys

from sanic import Blueprint
from sanic.response import html

from src.config import CONFIG

json_bp = Blueprint('rss_json', url_prefix='json')
json_bp.static('/statics/rss_json', CONFIG.BASE_DIR + '/statics/rss_json')

# jinjia2 config
env = Environment(
    loader=PackageLoader('views.rss_json', '../templates/rss_json'),
    autoescape=select_autoescape(['html', 'xml', 'tpl']),
    enable_async=enable_async)

@json_bp.route("/")
async def index(request):
    return await template('index.html') 
```

不知你是否感受到这样编写服务的好处，让我们列举下：

+   每个蓝图都有其自己定义的前缀，如 /html/ /json/

+   不同蓝图下面 route 可相同且互不冲突

+   html 以及 css 等文件可根据蓝图名称目录引用，条理清晰易扩展

+   模块化

+   ...

不多说，看运行效果：

```
cd /Sanic-For-Pythoneer/examples/demo04/sample01/src
python run.py 
```

现在，请访问：

+   http://0.0.0.0:8000/html/

+   http://0.0.0.0:8000/json/

+   http://0.0.0.0:8000/html/index

+   http://0.0.0.0:8000/json/index

感觉这个设计方便了全世界^_^  ## 说明

蓝图的具体使用还请诸位多多摸索，说不定能发掘出更多好玩的玩法以及更加优雅的编码方式，本章的代码地址：[demo04](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo04/]  # 数据库使用

介绍中说的很明白，`Sanic` 是一个可以使用 `async/await` 语法编写项目的**异步**非阻塞框架，既然是异步框架，那么在使用过程中用到的第三方包也最好是异步的，比如 http 请求，最好就使用`aihttp`而非`requests`，对于数据库的连接，也是同样如此，下面我将用代码的形式来说明下如何在 Sanic 中连接数据库。

## 操作 Mysql

对于 mysql 数据库的异步操作，我只在一些脚本中用过，用的是[aiomysql](https://github.com/aio-libs/aiomysql) [https://github.com/aio-libs/aiomysql]，其中官方文档中讲得很清楚，也支持结合`sqlalchemy`编写`ORM`，然后 aiomysql 提供了自己编写的异步引擎。

```
from aiomysql.sa import create_engine
# 这个才是关键 
```

下面我编写一个具体的例子来用异步语句操作下数据库，首先建立如下目录：

```
aio_mysql
├── demo.py
├── model.py
└── requirements.txt 
```

建立表：

```
create database test_mysql;

CREATE TABLE user
(
  id        INT AUTO_INCREMENT
    PRIMARY KEY,
  user_name VARCHAR(16) NOT NULL,
  pwd       VARCHAR(32) NOT NULL,
  real_name VARCHAR(6)  NOT NULL
); 
```

一切准备就绪，下面编写代码：

```
# script: model.py
import sqlalchemy as sa

metadata = sa.MetaData()

user = sa.Table(
    'user',
    metadata,
    sa.Column('id', sa.Integer, autoincrement=True, primary_key=True),
    sa.Column('user_name', sa.String(16), nullable=False),
    sa.Column('pwd', sa.String(32), nullable=False),
    sa.Column('real_name', sa.String(6), nullable=False),
)

# script: demo.py
import asyncio

from aiomysql.sa import create_engine

from model import user,metadata

async def go(loop):
    """
 aiomysql 项目地址：https://github.com/aio-libs/aiomysql
 :param loop:
 :return:
 """
    engine = await create_engine(user='root', db='test_mysql',
                                 host='127.0.0.1', password='123456', loop=loop)
    async with engine.acquire() as conn:
        await conn.execute(user.insert().values(user_name='user_name01', pwd='123456', real_name='real_name01'))
        await conn.execute('commit')

        async for row in conn.execute(user.select()):
            print(row.user_name, row.pwd)

    engine.close()
    await engine.wait_closed()

loop = asyncio.get_event_loop()
loop.run_until_complete(go(loop)) 
```

运行 python demo.py，会看到如下输出：

```
user_name01 123456 
```

很简单吧，具体示例见[aio_mysql](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05/aio_mysql) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05/aio_mysql]，如果你比较喜欢类似 SQLAlchemy 的操作方式，这里推荐一个异步 ORM，[gino](https://github.com/fantix/gino) [https://github.com/fantix/gino]。  ## 操作 MongoDB

我业余写的一个项目，基本用的就是`MongoDB`来储存数据，对于异步操作`MongoDB`，目前 Python 主要用的是[motor](https://motor.readthedocs.io/en/stable/index.html) [https://motor.readthedocs.io/en/stable/index.html]，使用起来依旧很简单，但是结合具体功能，就有不同的需求，最后就会形成各种各样的连接方案，这里我主要分享下自己是如何使用的，目录如下所示：

```
aio_mongo
├── demo.py
└── requirements.txt 
```

`MongoDB`是一个基于分布式文件存储的数据库，它介于关系数据库和非关系数据库之间，所以它使用起来也是比较灵活的，打开`demo.py`：

```
#!/usr/bin/env python
import os

from functools import wraps

from motor.motor_asyncio import AsyncIOMotorClient

MONGODB = dict(
    MONGO_HOST=os.getenv('MONGO_HOST', ""),
    MONGO_PORT=os.getenv('MONGO_PORT', 27017),
    MONGO_USERNAME=os.getenv('MONGO_USERNAME', ""),
    MONGO_PASSWORD=os.getenv('MONGO_PASSWORD', ""),
    DATABASE='test_mongodb',
)

class MotorBaseOld:
    """
 默认实现了一个 db 只创建一次，缺点是更换集合麻烦
 """
    _db = None
    MONGODB = MONGODB

    def client(self, db):
        # motor
        self.motor_uri = 'mongodb://{account}{host}:{port}/{database}'.format(
            account='{username}:{password}@'.format(
                username=self.MONGODB['MONGO_USERNAME'],
                password=self.MONGODB['MONGO_PASSWORD']) if self.MONGODB['MONGO_USERNAME'] else '',
            host=self.MONGODB['MONGO_HOST'] if self.MONGODB['MONGO_HOST'] else 'localhost',
            port=self.MONGODB['MONGO_PORT'] if self.MONGODB['MONGO_PORT'] else 27017,
            database=db)
        return AsyncIOMotorClient(self.motor_uri)

    @property
    def db(self):
        if self._db is None:
            self._db = self.client(self.MONGODB['DATABASE'])[self.MONGODB['DATABASE']]

        return self._db 
```

我最开始，使用的是这种方式来连接`MongoDB`，上面代码保证了集合中的 db 被 _db 维护，保证只会创建一次，如果你项目中不会随意更改集合的话，也没什么大问题，如果不是，我推荐使用下面这样的连接方式，可以自由地更换集合与 db：

```
 def singleton(cls):
    """
 用装饰器实现的实例 不明白装饰器可见附录 装饰器：https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part2/%E9%99%84%E5%BD%95%EF%BC%9A%E5%85%B3%E4%BA%8E%E8%A3%85%E9%A5%B0%E5%99%A8.md
 :param cls: cls
 :return: instance
 """
    _instances = {}

    @wraps(cls)
    def instance(*args, **kw):
        if cls not in _instances:
            _instances[cls] = cls(*args, **kw)
        return _instances[cls]

    return instance

@singleton
class MotorBase:
    """
 更改 mongodb 连接方式 单例模式下支持多库操作
 About motor's doc: https://github.com/mongodb/motor
 """
    _db = {}
    _collection = {}
    MONGODB = MONGODB

    def __init__(self):
        self.motor_uri = ''

    def client(self, db):
        # motor
        self.motor_uri = 'mongodb://{account}{host}:{port}/{database}'.format(
            account='{username}:{password}@'.format(
                username=self.MONGODB['MONGO_USERNAME'],
                password=self.MONGODB['MONGO_PASSWORD']) if self.MONGODB['MONGO_USERNAME'] else '',
            host=self.MONGODB['MONGO_HOST'] if self.MONGODB['MONGO_HOST'] else 'localhost',
            port=self.MONGODB['MONGO_PORT'] if self.MONGODB['MONGO_PORT'] else 27017,
            database=db)
        return AsyncIOMotorClient(self.motor_uri)

    def get_db(self, db=MONGODB['DATABASE']):
        """
 获取一个 db 实例
 :param db: database name
 :return: the motor db instance
 """
        if db not in self._db:
            self._db[db] = self.client(db)[db]

        return self._db[db]

    def get_collection(self, db_name, collection):
        """
 获取一个集合实例
 :param db_name: database name
 :param collection: collection name
 :return: the motor collection instance
 """
        collection_key = db_name + collection
        if collection_key not in self._collection:
            self._collection[collection_key] = self.get_db(db_name)[collection]

        return self._collection[collection_key] 
```

为了避免重复创建 MotorBase 实例，可以实现一个单例模式来保证资源的有效利用，具体代码以及运行 demo 见[aio_mongo](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05/aio_mongo) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05/aio_mongo]  ## 操作 Redis

对于 Redis 的异步操作，我选用的是`asyncio_redis`，你大可不必非要使用这个，或许其他的库实现地更好，我只是用这个举个例子，建立如下目录：

```
aio_redis
├── demo.py
└── requirements.txt 
```

建立一个 redis 连接池：

```
#!/usr/bin/env python
import os
import asyncio_redis

REDIS_DICT = dict(
    IS_CACHE=True,
    REDIS_ENDPOINT=os.getenv('REDIS_ENDPOINT', "localhost"),
    REDIS_PORT=os.getenv('REDIS_PORT', 6379),
    REDIS_PASSWORD=os.getenv('REDIS_PASSWORD', None),
    DB=0,
    POOLSIZE=10,
)

class RedisSession:
    """
 建立 redis 连接池
 """
    _pool = None

    async def get_redis_pool(self):
        if not self._pool:
            self._pool = await asyncio_redis.Pool.create(
                host=str(REDIS_DICT.get('REDIS_ENDPOINT', "localhost")), port=int(REDIS_DICT.get('REDIS_PORT', 6379)),
                poolsize=int(REDIS_DICT.get('POOLSIZE', 10)), password=REDIS_DICT.get('REDIS_PASSWORD', None),
                db=REDIS_DICT.get('DB', None)
            )

        return self._pool 
```

具体见[aio_redis](https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/examples/demo05/aio_redis/demo.py) [https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/examples/demo05/aio_redis/demo.py]，使用起来很简单，不做多叙述。  ## 说明

如果你使用其它类型的数据库，其实使用方式也是类似。 本章代码地址，见[demo05](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo05]  # 常用的技巧

结合前面讲的配置、项目结构、页面渲染、数据库连接，构造一个优雅的 Sanic 应用对你来说估计没什么大问题了，但是在实际使用过程中，可能你会碰到各种各样的需求，与之对应，你也会遇到千奇百怪的问题，除了在官方 pro 提 issue，你大部分问题都需要自己去面对，看官方的介绍：

> Async Python 3.5+ web server that's written to go fast

大概就可以明白`Sanic`框架的重心不会放在诸如`session cache reload authorized`这些问题上。

此篇我会将我遇到的一些问题以及解决方案一一记录下来，估计会持续更新，因为问题是不断的哈哈，可能有些问题与前面讲的有些重复，你大可略过，我将其总结成一些小技巧，供大家参考，具体如下：

+   api 请求 json 参数以及 api 接口验证

+   gRPC 的异步调用方式

+   Blueprint

+   html&templates 编写

+   cache

+   热加载

+   session

对于一些问题，我将编写一个小服务来演示这些技巧，具体见[demo06](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06]，依旧使用前面 rss 的那个例子，经过修改一番后的 rss 例子现在目录变成这样子了，里面加了我遇到的各种问题的解决方案，或许你只需要关注你想要了解的就好，如果你有其他的问题，欢迎 issue 提问，目录大概如下所示：

```
src
├── config
│   ├── __init__.py
│   ├── config.py
│   ├── dev_config.py
│   └── pro_config.py
├── database
│   ├── __init__.py
│   └── redis_base
├── grpc_service
│   ├── __init__.py
│   ├── grpc_asyncio_client.py
│   ├── grpc_client.py
│   ├── grpc_server.py
│   ├── hello_grpc.py
│   ├── hello_pb2.py
│   ├── hello_pb2_grpc.py
│   └── proto
├── statics
│   ├── rss_html
│   │   ├── css
│   │   └── js
│   └── rss_json
│       ├── css
│       └── js
├── templates
│   ├── rss_html
│   └── rss_json
├── tools
│   ├── __init__.py
│   └── mid_decorator.py
├── views
│   ├── __init__.py
│   ├── rss_api.py
│   ├── rss_html.py
│   └── rss_json.py
└── run.py 
```

和前面相比，可以看到目录里面增加了几个目录和文件，一个是关于数据库的`database`，以及关于 gRPC 的`grpc_service`，其实主要是为了演示而已，如果想了解，就可以看关于 gRPC 的部分，不喜欢就看其他的。

增加的文件是`rss_json.py`，假设这是个接口文件吧，将会根据你的请求参数返回一串 json，具体还是建议直接去看代码吧，点这里[sample](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample]。

## 验证问题

假设你正在编写一个 api 服务，比如根据传的 blog 名字返回其 rss 数据，比如`rss_json.py`：

```
#!/usr/bin/env python
from feedparser import parse
from sanic import Blueprint
from sanic.response import json

api_bp = Blueprint('rss_api', url_prefix='v1')

@api_bp.route("/get/rss/<param>")
async def get_rss_json(request, param):
    if param == 'howie6879':
        url = "http://blog.howie6879.cn/atom.xml"
        feed = parse(url)
        articles = feed['entries']
        data = []
        for article in articles:
            data.append({"title": article["title_detail"]["value"], "link": article["link"]})
        return json(data)
    else:
        return json({'info': '请访问 http://0.0.0.0:8000/v1/get/rss/howie6879'}) 
```

启动服务后，此时用`GET`方式访问`http://0.0.0.0:8000/v1/get/rss/howie6879`，就会返回一串你需要的 json，这样使用，没什么问题，好，下面改成 post 请求，其中请求的参数如下：

```
{
    "name": "howie6879"
} 
```

在`rss_json.py`中加入一个新的视图函数：

```
@api_bp.route("/post/rss/", methods=['POST'])
async def post_rss_json(request, **kwargs):
    post_data = json_loads(str(request.body, encoding='utf-8'))
    name = post_data.get('name')
    if name == 'howie6879':
        url = "http://blog.howie6879.cn/atom.xml"
        feed = parse(url)
        articles = feed['entries']
        data = []
        for article in articles:
            data.append({"title": article["title_detail"]["value"], "link": article["link"]})
        return json(data)
    else:
        return json({'info': '参数错误'}) 
```

发送 post 请求到`http://0.0.0.0:8000/v1/post/rss/`，依旧和上面的结果一样，代码里面有个问题，我们需要判断`name`参数是不是存在于 post 过来的 data 中，解决方案很简单，加一个判断就好了，可这个是最佳方案么？

显然并不是的，如果有十个参数呢？然后再增加十几个路由呢？每个路由里有十个参数需要判断，想象一下，这样实施下来，难道要在代码里面堆积满屏幕的判断语句么？这样实在是太可怕了，我们需要更好更通用的解决方案，是时候写个装饰器来验证参数了，打开`mid_decorator.py`文件，添加一个验证的装饰器函数：

```
def auth_params(*keys):
    """
 api 请求参数验证
 :param keys: params
 :return:
 """

    def wrapper(func):
        @wraps(func)
        async def auth_param(request=None, rpc_data=None, *args, **kwargs):
            request_params, params = {}, []
            if isinstance(request, Request):
                # sanic request
                if request.method == 'POST':
                    try:
                        post_data = json_loads(str(request.body, encoding='utf-8'))
                    except Exception as e:
                        return response_handle(request, {'info': 'error'})
                    else:
                        request_params.update(post_data)
                        params = [key for key, value in post_data.items() if value]
                elif request.method == 'GET':
                    request_params.update(request.args)
                    params = [key for key, value in request.args.items() if value]
                else:
                    return response_handle(request, {'info': 'error'})
            else:
                pass

            if set(keys).issubset(set(params)):
                kwargs['request_params'] = request_params
                return await dec_func(func, request, *args, **kwargs)
            else:
                return response_handle(request, {'info': 'error'})

        return auth_param

    return wrapper

async def dec_func(func, request, *args, **kwargs):
    try:
        response = await func(request, *args, **kwargs)
        return response
    except Exception as e:
        return response_handle(request, {'info': 'error'}) 
```

注意，上面增加的路由函数改为这样：

```
@api_bp.route("/post/rss/", methods=['POST'])
@auth_params('name')
async def post_rss_json(request, **kwargs): 
```

这样一个请求进来，就会验证参数`name`是否存在，而在视图函数里面，就可以放心大胆地使用传进来的参数了，而且对于其他不同的参数验证，只要按照这个写法，直接增加验证参数就好，十分灵活方便。

对于请求验证的问题，解决方法也是类似，就是利用装饰器来实现，我自己也实现过，在上面的代码链接里面可以找到，不过现在的`Sanic`官方已经提供了`demo`，见[这里](https://github.com/channelcat/sanic/blob/master/examples/authorized_sanic.py) [https://github.com/channelcat/sanic/blob/master/examples/authorized_sanic.py]  ## gRPC 的异步调用方式

在编写微服务的时候，除了需要支持`http`请求外，一般还需要支持`gRPC`请求，我在使用`Sanic`编写微服务的时候，遇到关于异步请求`RPC`的需求，当时确实困扰了我，意外发现了这个库[grpclib](https://github.com/vmagamedov/grpclib) [https://github.com/vmagamedov/grpclib]，进入`src/grpc_service`目录，里面就是解决方案，很简单，这里就不多说了，直接看代码就好。  ## Blueprint

Blueprint 前面的章节有仔细聊过，这里不多说，借用官方文档的例子，一个简单的 sanic 服务就搭好了：

```
# main.py
from sanic import Sanic
from sanic.response import json

app = Sanic()

@app.route("/")
async def test(request):
    return json({"hello": "world"})

#访问 http://0.0.0.0:8000/即可
if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000) 
```

上面的例子可以当做一个完整的小应用，关于 Blueprint 的概念，可以这么理解，一个蓝图可以独立完成某一个任务，包括模板文件，静态文件，路由都是独立的，而一个应用可以通过注册许多蓝图来进行构建。 比如我现在编写的项目，我使用的是功能式架构，具体如下：

```
├── server.py
├── static
│   └── novels
│       ├── css
│       │   └── result.css
│       ├── img
│       │   └── read_content.png
│       └── js
│           └── main.js
├── template
│   └── novels
│       └── index.html
└── views
    └── novels_blueprint.py 
```

可以看到，总的 templates 以及静态文件还是放在一起，但是不同的 blueprint 则放在对应的文件夹中，还有一种分区式架构，则是将不同的 templats 以及 static 等文件夹全都放在不同的的 blueprint 中。 最后只要将每个单独的 blueprint 在主启动文件进行注册就好，上面的目录树是我以前的一个项目[owllook](https://github.com/howie6879/owllook) [https://github.com/howie6879/owllook]的，也是用`Sanic`编写的，有兴趣可以看看，不过现在结构改变挺大。  ## html&templates 编写

编写 web 服务，自然会涉及到 html，sanic 自带有 html 函数，但这并不能满足有些需求，故引入 jinja2 迫在眉睫，使用方法也很简单：

```
# 适用 python3.5+
# 代码片段，明白意思就好
from sanic import Blueprint
from jinja2 import Environment, PackageLoader, select_autoescape

# 初始化 blueprint 并定义静态文件夹路径
bp = Blueprint('novels_blueprint')
bp.static('/static', './static/novels')

# jinjia2 config
env = Environment(
    loader=PackageLoader('views.novels_blueprint', '../templates/novels'),
    autoescape=select_autoescape(['html', 'xml', 'tpl']))

def template(tpl, **kwargs):
    template = env.get_template(tpl)
    return html(template.render(kwargs))

@bp.route("/")
async def index(request):
    return template('index.html', title='index') 
```

如果是`python3.6`，可以试试下面的写法：

```
# 适用 python3.5+
# 代码片段，明白意思就好
#!/usr/bin/env python
import sys

from feedparser import parse
from jinja2 import Environment, PackageLoader, select_autoescape
from sanic import Blueprint
from sanic.response import html

from src.config import CONFIG

# https://github.com/channelcat/sanic/blob/5bb640ca1706a42a012109dc3d811925d7453217/examples/jinja_example/jinja_example.py
# 开启异步特性  要求 3.6+
enable_async = sys.version_info >= (3, 6)

html_bp = Blueprint('rss_html', url_prefix='html')
html_bp.static('/statics/rss_html', CONFIG.BASE_DIR + '/statics/rss_html')

# jinjia2 config
env = Environment(
    loader=PackageLoader('views.rss_html', '../templates/rss_html'),
    autoescape=select_autoescape(['html', 'xml', 'tpl']),
    enable_async=enable_async)

async def template(tpl, **kwargs):
    template = env.get_template(tpl)
    rendered_template = await template.render_async(**kwargs)
    return html(rendered_template) 
```  ## 缓存

我在项目中主要使用 redis 作为缓存，使用[aiocache](https://github.com/argaen/aiocache) [https://github.com/argaen/aiocache]很方便就完成了我需要的功能，当然自己利用 aioredis 编写也不会复杂到哪里去。

比如上面的例子，每次访问`http://0.0.0.0:8000/v1/get/rss/howie6879`，都要请求一次对应的 rss 资源，如果做个缓存那岂不是简单很多？

改写成这样：

```
@cached(ttl=1000, cache=RedisCache, key="rss", serializer=PickleSerializer(), port=6379, namespace="main")
async def get_rss():
    print("第一次请求休眠 3 秒...")
    await asyncio.sleep(3)
    url = "http://blog.howie6879.cn/atom.xml"
    feed = parse(url)
    articles = feed['entries']
    data = []
    for article in articles:
        data.append({"title": article["title_detail"]["value"], "link": article["link"]})
    return data

@api_bp.route("/get/rss/<name>")
async def get_rss_json(request, name):
    if name == 'howie6879':
        data = await get_rss()
        return json(data)
    else:
        return json({'info': '请访问 http://0.0.0.0:8000/v1/get/rss/howie6879'}) 
```

为了体现缓存的速度，首次请求休眠 3 秒，请求过后，redis 中就会将此次 json 数据缓存进去了，下次去请求就会直接冲 redis 读取数据。

带上装饰器，什么都解决了。  ## 热加载

我发现有个 pr 实现了这个需求，如果你有兴趣，可以看[这里](https://github.com/channelcat/sanic/pull/1047) [https://github.com/channelcat/sanic/pull/1047]  ## 会话

sanic 对此有一个第三方插件[`sanic_session`](https://github.com/subyraman/sanic_session) [https://github.com/subyraman/sanic_session]，用法非常简单，有兴趣可以看看  # 7\. 可靠的扩展

目前开源社区有不少人为`Sanic`框架编写了插件，这些插件很可能会在将来的某个时间帮助到你，比如缓存、模板渲染、api 文档生成、Session...等等

官方也维护了一个扩展列表，见[扩展](http://sanic.readthedocs.io/en/latest/sanic/extensions.html) [http://sanic.readthedocs.io/en/latest/sanic/extensions.html]  # 9\. 测试与部署

在项目结构那一节说过，一个服务的基本结构大概是怎么样的，这里再列出来回顾下：

```
pro_name
├── docs            # 项目文档说明
├── src or pro_name/# 项目名称
├── tests           # 测试用例
├── README.md       # 项目介绍
└──requirements.txt # 该项目依赖的第三方库 
```

一个服务编写完成后，在部署之前，你需要做的一步就是进行单元测试，首先你要确定目前的代码是可以完美运行的，然后测试用例还可以让你在下次修改代码逻辑进行版本迭代的时候，只要再跑一次对应的测试用例就可以快速地确定此次的版本依旧是完美的，大大节省时间，一般集成测试的时候都需要跑测试用例的脚本。

本次使用的例子还是继续在[demo06](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample]的基础上进行演示，提醒一下诸位，在继续阅读前可以先大致看下目录中`test`的代码哈。

## 9\. 测试

### 9\. 单元测试

Sanic 进行单元测试的时候，官方推荐使用的是 [pytest](https://github.com/pytest-dev/pytest) [https://github.com/pytest-dev/pytest]，具体怎么对 Sanic 构建的服务进行测试呢，别急，Sanic 开发团队提供了关于 `pytest` 的插件，见 [pytest-sanic](https://github.com/yunstanford/pytest-sanic) [https://github.com/yunstanford/pytest-sanic]，使用起来也是非常简单。

让我们结合前面的例子，利用 [pytest-sanic](https://github.com/yunstanford/pytest-sanic) [https://github.com/yunstanford/pytest-sanic] 测试一下 [demo06](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample] 中的 `rss api` 服务，先看下目录结构：

```
tests
├── setting.py
└── test_rss.py 
```

首先在 `setting.py` 中定好请求的数据：

```
# setting.py
def rss_data():
    return {
        "name": "howie6879"
    } 
```

然后编写对应的测试用例，这里是关于 `/v1/post/rss/` 的一个 `POST` 请求测试，代码如下：

```
# test_rss.py
async def test_http_rss(test_cli):
    data = setting.rss_data()
    response = await test_cli.post('/v1/post/rss/', data=ujson.dumps(data))
    resp_json = await response.json()
    assert resp_json['status'] == 1

# 运行测试 pytest tests/test_rss.py
"""
================================================= test session starts ==================================================
platform darwin -- Python 3.6.0, pytest-3.2.3, py-1.4.34, pluggy-0.4.0
rootdir: /Users/howie/Documents/programming/python/git/Sanic-For-Pythoneer/examples/demo06/sample, inifile:
plugins: celery-4.0.2, sanic-0.1.5
collected 2 items

tests/test_rss.py .s

========================================= 1 passed, 1 skipped in 2.13 seconds ==========================================
""" 
```

可以看到测试通过，全部测试代码在 [这里](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample/tests) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample/tests]，最好可以直接 clone 下来跑一遍，细心的朋友可能注意到了测试用例结果中的这句话 `1 passed, 1 skipped in 2.13 seconds`，为什么会有一个测试跳过呢？

因为在实际编写项目的过程中，你的测试用例很可能会分好多种，比如在编写微服务的过程中，同样一套处理逻辑，你需要分别实现 `HTTP` 和 `gRPC` 两种调用方式，测试代码里面我就多写了一个测试 `gRPC` 的配置，不过我设置了参数： `DIS_GRPC_TEST = True`，没有启用 `gRPC` 的测试，这里只是举个例子，具体还是要看诸位的需求，用本次的例子作为参考，就算改动起来也并没什么难度。  ### 9\. 压力测试

说完了如何对 Sanic 编写的服务进行单元测试，接下来稍微讲下如何进行压力测试，压力测试最好在内外网都进行测试下，当然服务器配置是你定，然后在多个服务器上部署好服务，启动起来，利用负载均衡给压测代码一个固定的 ip，这样对于服务的水平扩展测试就会很方便。

压测可以考虑使用 [locust](https://github.com/locustio/locust) [https://github.com/locustio/locust]，看看现在 `tests` 下的目录结构：

```
├── locust_rss
│   ├── __init__.py
│   ├── action.py
│   ├── locust_rss_http.py
│   ├── locustfile.py
│   └── utils.py
├── setting.py
└── test_rss.py 
```

新增了 `locust_rss` 文件夹，首先在 `action.py` 定义好请求地址与请求方式：

```
HTTP_URL = "http://0.0.0.0:8000/v1/post/rss/"
GRPC_URL = "0.0.0.0:8990"

def json_requests(client, data, url):
    func_name = inspect.stack()[1][3]
    headers = {'content-type': 'application/json'}
    return post_request(client, data=json.dumps(data), url=url, func_name=func_name, headers=headers)

def action_rss(client):
    data = {
        "name": "howie6879"
    }
    json_requests(client, data, HTTP_URL) 
```

压测怎么个压测法，请求哪些接口，接口请求怎么分配，都在 `locust_rss_http.py` 里定好了：

```
class RssBehavior(TaskSet):
    @task(1)
    def interface_rss(self):
        action.action_rss(self.client) 
```

然后需要发送请求给目标，还需要判断是否请求成功，这里将其封装成函数，放在 `utils.py` 里，比如 `post_request` 函数：

```
def post_request(client, data, url, func_name=None, **kw):
    """
 发起 post 请求
 """
    func_name = func_name if func_name else inspect.stack()[1][3]
    with client.post(url, data=data, name=func_name, catch_response=True, timeout=2, **kw) as response:
        result = response.content
        res = to_json(result)
        if res['status'] == 1:
            response.success()
        else:
            response.failure("%s-> %s" % ('error', result))
        return result 
```

`locustfile.py` 是压测的启动文件，��不可少，我们先请求一次，看看能不能请求成功，如果成功了再将其正式运行起来：

```
cd Sanic-For-Pythoneer/examples/demo06/sample/tests/locust_rss

# 只想跑一次看看有没有问题 记得先将你编写的服务启动起来哦
locust -f locustfile.py --no-web -c 1 -n 1

# Output: 表示没毛病
[2018-01-14 14:54:30,119] 192.168.2.100/INFO/locust.main: Shutting down (exit code 0), bye.
 Name                                                          # reqs      # fails     Avg     Min     Max  |  Median   req/s
--------------------------------------------------------------------------------------------------------------------------------------------
 POST action_rss                                                    1     0(0.00%)    1756    1756    1756  |    1800    0.00
--------------------------------------------------------------------------------------------------------------------------------------------
 Total                                                              1     0(0.00%)                                       0.00

Percentage of the requests completed within given times
 Name                                                           # reqs    50%    66%    75%    80%    90%    95%    98%    99%   100%
--------------------------------------------------------------------------------------------------------------------------------------------
 POST action_rss                                                     1   1800   1800   1800   1800   1800   1800   1800   1800   1756
-------------------------------------------------------------------------------------------------------------------------------------------- 
```

好了，没问题了，可以执行 `locust -f locustfile.py`，然后访问 `http://0.0.0.0:8089/`，如下图：

![locust](img/01.jpg)

当然，这里只是大概讲解下如何进行压测，至于真实环境下，还是需要诸位继续摸索。

千辛万苦，终于到了这一步，我们历经代码编写、单元测试、压力测试终于到了这一步，将我们的服务正式部署！

在继续阅读之前，请你万万先读一遍 [官方的 Deploying](http://sanic.readthedocs.io/en/latest/sanic/deploying.html) [http://sanic.readthedocs.io/en/latest/sanic/deploying.html]。

好了，你现在肯定知道了 Sanic 服务的两种启动方式，分别如下：

+   `python -m sanic server.app --host=0.0.0.0 --port=8000 --workers=4`

+   运行 `gunicorn myapp:app --bind 0.0.0.0:8000 --worker-class sanic.worker.GunicornWorker`

至于选哪种启动方式，我觉得都可以，看你心情了，下面直接说下如何部署：

+   Gunicorn + Supervisor + Caddy

+   Docker

对于用 Gunicorn 启动，可以将配置写在自己定义的配置文件中，比如 `config/gunicorn.py`：

```
# gunicorn.py
bind = '127.0.0.1:8001'
backlog = 2048

workers = 2
worker_connections = 1000
timeout = 30
keepalive = 2

spew = False
daemon = False
umask = 0 
```

然后直接运行 `gunicorn -c config/gunicorn.py --worker-class sanic.worker.GunicornWorker server:app` 就启动了。

为了方便对此服务的管理，可以使用 `Supervisor` 来对服务进行启动、停止，比如使用如下配置：

```
[program:demo]
command      = gunicorn -c config/gunicorn.py --worker-class sanic.worker.GunicornWorker server:app
directory    = /your/path/
user         = root
process_name = %(program_name)s
autostart    = true
autorestart  = true
startsecs    = 3
redirect_stderr         = true
stdout_logfile_maxbytes = 500MB
stdout_logfile_backups  = 10
stdout_logfile          = ~/supervisor/demo.log
environment             = MODE="PRO" 
```

最后，你需要对该服务(假设是一个网站)的"站点"进行配置，推荐使用 Caddy 服务器，[Caddy](https://github.com/mholt/caddy) [https://github.com/mholt/caddy] 是使用 Go 编写的 Web 服务器，它简单易用且支持自动化 HTTPS，你只需按照官方文档编写好你自己的 Caddyfile，比如目前的例子：

```
www.your.domain.com {
    proxy / 127.0.0.1:8001
    timeouts none
    gzip
}

your.domain.com {
    redir http://www.your.domain.com
} 
```

在利用 `Supervisor` 守护一个 Caddy 的服务进程，至此，你的服务站点就搭建好了。

现在 `Docker` 的崛起，使得我们的部署方式也发生了改变，我们完全可以将上面编写的服务 `Docker` 化，然后构建自己的集群，一个服务器启动一个服务节点，再启动一个镜像做负载均衡，岂不是美滋滋。

这个例子中我已经写了一个[Dockerfile](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample/Dockerfile) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample/Dockerfile]，你可以按照如下方式进行启动：

```
docker build -t demo:0.1 .
docker run -d -p 8001:8001 demo:0.1 
```

我建议使用`daocloud`来体验一下，你可以关联自己主机，不一定非要用我这个例子中的服务镜像，你大可随意下载一个镜像  # 9\. 说明

代码见[demo06](https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample) [https://github.com/howie6879/Sanic-For-Pythoneer/tree/master/examples/demo06/sample]  # 10\. 第一部分: 技巧
