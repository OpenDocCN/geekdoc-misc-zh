# 第二部分: 源码及附录

+   1\. 第二部分: 源码及附录

+   2\. Sanic 源码阅读：基于 0.1.2

    +   simple_server.py

    +   blueprints.py

    +   总结

+   3\. 附录：关于装饰器

    +   认识装饰器

    +   装饰器原理

    +   结语

# 1\. 第二部分: 源码及附录  # 2\. Sanic 源码阅读：基于 0.1.2

`Sanic`是一个可以使用`async/await`语法编写项目的异步非阻塞框架，它写法类似于`Flask`，但使用了异步特性，而且还使用了`uvloop`作为事件循环，其底层使用的是`libuv`，从而使 `Sanic`的速度优势更加明显。

本章，我将和大家一起看看`Sanic`里面的运行机制是怎样的，它的`Router Blueprint`等是如何实现的。

如果你有以下的需求：

+   想深入了解 Sanic，迫切想知道它的运行机制

+   直接阅读源码，做一些定制

+   学习

将 Sanic-0.1.2 阅读完后的一些建议，我觉得你应该有以下基础再阅读源码才会理解地比较好：

+   理解[装饰器](https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part2/%E9%99%84%E5%BD%95%EF%BC%9A%E5%85%B3%E4%BA%8E%E8%A3%85%E9%A5%B0%E5%99%A8.md) [https://github.com/howie6879/Sanic-For-Pythoneer/blob/master/docs/part2/%E9%99%84%E5%BD%95%EF%BC%9A%E5%85%B3%E4%BA%8E%E8%A3%85%E9%A5%B0%E5%99%A8.md]，见附录

+   理解协程

Sanic-0.1.2 的核心文件如下：

```
.
├── __init__.py
├── blueprints.py
├── config.py
├── exceptions.py
├── log.py
├── request.py
├── response.py
├── router.py
├── sanic.py
├── server.py
└── utils.py 
```

通过运行下面的示例，这些文件都会被我们看到它的作用，拭目以待吧，为了方便诸位的理解，我已将我注解的一份`Sanic`代码上传到了`github`，见[sanic_annotation](https://github.com/howie6879/sanic_annotation) [https://github.com/howie6879/sanic_annotation]。

## simple_server.py

让我们从[simple_server](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/examples/simple_server.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/examples/simple_server.py]开始吧，代码如下：

```
 from sanic_0_1_2.src import Sanic
from sanic_0_1_2.src.response import json

app = Sanic(__name__)

@app.route("/")
async def test(request):
    return json({"test": True})

app.run(host="0.0.0.0", port=8000) 
```

或许你直接把[sanic_annotation](https://github.com/howie6879/sanic_annotation) [https://github.com/howie6879/sanic_annotation]项目直接 clone 到本地比较方便调试+理解：

```
git clone https://github.com/howie6879/sanic_annotation
cd sanic_annotation/sanic_0_1_2/examples/ 
```

那么，现在一切准备就绪，开始阅读吧。

前两行代码导入包：

+   `Sanic`：构建一个 Sanic 服务必须要实例化的类

+   `json`：以 json 格式返回结果，实际上是 HTTPResponse 类，根据实例化参数 content_type 的不同，构建不同的实例，如：

    +   `text`：`content_type="text/plain; charset=utf-8"`

    +   `html`：`content_type="text/html; charset=utf-8"`

实例化一个`Sanic`对象，`app = Sanic(__name__)`，可见[sanic.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/sanic.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/sanic.py]，我已经在这个文件里面做了一些注释，这里也详细说下`Sanic`类：

+   route()：装饰器，构建 uri 和视图函数的映射关系，调用 Router().add()方法

+   exception()：装饰器，和上面差不多，不过针对的是错误处理类 Handler

+   middleware()：装饰器，针对中间件

+   register_blueprint()：注册视图的函数，接受第一个参数是视图类`blueprint`，再调用该类下的`register`方法实现将此蓝图下的`route、exception、middleware`统一注册到`app.route、app.exception、app.exception`

+   handle_request()：这是一个很重要的异步函数，当服务启动后，如果客户端发来一个有效的请求，会自动执行 `on_message_complete`函数，该函数的目的是异步调用 `handle_request`函数，`handle_request`函数会回调`write_response`函数，`write_response`接受的参数是此 uri 请求对应的视图函数，比如上面 demo 中，如果客户端请求'/'，那么这里`write_response`就会接受`json({"test": True})`，然后进一步处理，再返回给客户端

+   run()：Sanic 服务的启动函数，必须执行，实际上会继续调用`server.serve`函数，详情下面会详细讲

+   stop()：终止服务

其实上面这部分介绍已经讲了 Sanic 基本的运行逻辑，如果你理解了，那下面的讲解对你来说是轻轻松松，如果不怎么明白，也不要紧，这是只是一个大体的介绍，跟着步骤来，也很容易理解，继续看代码：

```
# 此处将路由 / 与视图函数 test 关联起来
@app.route("/")
async def test(request):
    return json({"test": True}) 
```

`app.route`，上面介绍过，随着 Sanic 服务的启动而启动，可定义参数`uri, methods`

目的是为`url`的`path`和视图函数对应起来，构建一对映射关系，本例中`Sanic.router`类下的`Router.routes = []`

会增加一个名为`Route`的`namedtuple`，如下：

```
[Route(handler=<function test at 0x10a0f6488>, methods=None, pattern=re.compile('^/$'), parameters=[])] 
```

看到没，`uri '/'` 和视图函数`test`对应起来了，如果客户端请求`'/'`，当服务器监听到这个请求的时候,`handle_request`可以通过参数中的`request.url`来找到视图函数`test`并且执行，随即生成视图返回

那么这里`write_response`就会接受视图函数 test 返回的`json({"test": True})`

说下`Router`类，这个类的目的就是添加和获取路由对应的视图函数，把它想象成`dict`或许更容易理解：

+   add(self, uri, methods, handler)：添加一个映射关系到 self.routes

+   get(self, request)：获取 request.url 对应的视图函数

最后一行，`app.run(host="0.0.0.0", port=8000)`，Sanic 下的`run`函数，启动一个`http server`，���要是启动`run`里面的`serve`函数，参数如下：

```
 try:
    serve(
        host=host,
        port=port,
        debug=debug,
        # 服务开始后启动的函数
        after_start=after_start,
        # 在服务关闭前启动的函数
        before_stop=before_stop,
        # Sanic(__name__).handle_request()
        request_handler=self.handle_request,
        # 默认读取 Config
        request_timeout=self.config.REQUEST_TIMEOUT,
        request_max_size=self.config.REQUEST_MAX_SIZE,
    )
except:
    pass 
```

让我们将目光投向[server.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py]，这也是 Sanic 框架的核心代码：

+   serve()：里面会创建一个 TCP 服务的协程，然后通过`loop.run_forever()`运行这个事件循环，以便接收客户端请求以及处理相关事件，每当一个新的客户端建立连接服务就会创建一个新的`Protocol`实例，接受请求与返回响应离不开其中的`HttpProtocol`，里面的函数支持接受数据、处理数据、执行视图函数、构建响应数据并返回给客户端

+   HttpProtocol：`asyncio.Protocol`的子类，用来处理与客户端的通信，我在[server.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py]里写了对应的注释

至此，Sanic 服务启动了

不要小看这一个小小的 demo，执行一下，竟然涉及到下面这么多个文件，让我们总结一下：

+   [sanic.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/sanic.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/sanic.py]

+   [server.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/server.py]

+   [router.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/router.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/router.py]

+   [request.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/request.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/request.py]

+   [response.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/response.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/response.py]

+   [exceptions.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/exceptions.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/exceptions.py]

+   [config.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/config.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/config.py]

+   [log.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/log.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/log.py]

除去`__init__.py`，`Sanic`项目一共就 10 个文件，这个小 demo 不显山不露水地竟然用到了 8 个，虽然其中几个没有怎么用到，但也足够说明，你如果理解了这个 demo，`Sanic`的运行逻辑以及框架代码你已经了解地很深入了  ## blueprints.py

这个例子看完，我们就能轻易地明白什么是`blueprints`，以及`blueprints`的运行方式，代码如下：

```
 from sanic_0_1_2.src import Sanic
# 引入 Blueprint
from sanic_0_1_2.src import Blueprint
from sanic_0_1_2.src.response import json, text

app = Sanic(__name__)
blueprint = Blueprint('name', url_prefix='/my_blueprint')
blueprint2 = Blueprint('name2', url_prefix='/my_blueprint2')

@blueprint.route('/foo')
async def foo(request):
    return json({'msg': 'hi from blueprint'})

@blueprint2.route('/foo')
async def foo2(request):
    return json({'msg': 'hi from blueprint2'})

app.register_blueprint(blueprint)
app.register_blueprint(blueprint2)

app.run(host="0.0.0.0", port=8000, debug=True) 
```

让我们从这两行开始：

```
 blueprint = Blueprint('name', url_prefix='/my_blueprint')
blueprint2 = Blueprint('name2', url_prefix='/my_blueprint2') 
```

显然，`blueprint`以及`blueprint2`是`Blueprint`根据不同的参数生成的不同的实例对象，接下来要干嘛？没错，分析[blueprints.py](https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/blueprints.py) [https://github.com/howie6879/sanic_annotation/blob/master/sanic_0_1_2/src/blueprints.py]:

+   BlueprintSetup：蓝图注册类

    +   add_route：添加路由到 app

    +   add_exception：添加对应抛出的错误到 app

    +   add_middleware：添加中间件到 app

+   Blueprint：蓝图类，接收两个参数：name(蓝图名称) url_prefix 该蓝图的 url 前缀

    +   route：路由装饰器，将会生成一个匿名函数到 self.deferred_functions 列表里稍后一起处理注册到 app 里

    +   middleware：同上

    +   exception：同上

    +   record：注册一个回调函数到 self.deferred_functions 列表里面，

    +   make_setup_state：实例化 BlueprintSetup

    +   register：注册视图，实际就是注册 route、middleware、exception 到 app，此时会利用 make_setup_state 返回的 BlueprintSetup 示例进行对于的 add_***一系列操作，相当于 Sanic().route()效果

请看下`route`和`register`函数，然后再看下面的代码：

```
# 生成一个匿名函数到 self.deferred_functions 列表里 包含三个参数 handler(foo), uri, methods
@blueprint.route('/foo')
async def foo(request):
    return json({'msg': 'hi from blueprint'})

@blueprint2.route('/foo')
async def foo2(request):
    return json({'msg': 'hi from blueprint2'})

# 上一个例子说过这个函数，Sanic().register_blueprint() 注册蓝图
app.register_blueprint(blueprint)
app.register_blueprint(blueprint2) 
```

怎么样，现在来看，是不是很轻松，这一行`app.run(host="0.0.0.0", port=8000, debug=True)`服务启动代码不用多说吧？  ## 总结

看到这里，相信你已经完全理解了`Sanic`的运行机制，虽然还有`middleware&exception`的注册以及调用机制没讲，但这和`route`的运行机制一样，如果你懂了`route`那么这两个也很简单。

如果诸位一遍没怎么看明白，这里我建议可以多看几遍，多结合编辑器`Debug`下源码，坚持下来，会发下`Sanic`真的很简单，当然，这只是第一个小版本的`Sanic`，和目前的版本相比，不论是代码结构的复杂程度以及功能对比，都有很大差距，毕竟，`Sanic`一直在开源工作者的努力下，慢慢成长。

本人技术微末，若有错误，请指出，不胜感激.

+   注解地址：[sanic_annotation](https://github.com/howie6879/sanic_annotation) [https://github.com/howie6879/sanic_annotation]

+   博客地址：[`blog.howie6879.cn/post/31/`](http://blog.howie6879.cn/post/31/)  # 附录：关于装饰器

## 认识装饰器

在 python 中，对于一个函数，若想在其运行前后做点什么，那么装饰器是再好不过的选择，这种语法在一些项目中十分常见，是 Python 语言的黑魔法，用处颇多，话不多说，让我们看一下代码：

```
 #!/usr/bin/env
# -*-coding:utf-8-*-
# script: 01.py
__author__ = 'howie'
from functools import wraps
def decorator(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        print("%s was called" % func.__name__)
        func(*args, **kwargs)
    return wrapper
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello() 
```

```
outputs:
hello was called
Hello howie! 
```

这段代码，初看之下，确实不是很理解，接下来一步一步分析，看看装饰器到底是怎么工作的。  ## 装饰器原理

在 python 中，方法允许作为参数传递，想在某个函数执行前后加点料，也可以这样简单实现。

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-1.py
__author__ = 'howie'
def decorator(func):
    print("%s was called" % func.__name__)
    func()
def hello(name="howie"):
    print("Hello %s!" % name)
decorator(hello) 
```

由此，上面代码也可以这样写：

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-2.py
__author__ = 'howie'
def decorator(func):
    print("%s was called" % func.__name__)
    func()
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello 
```

两段代码执行后：

```
outputs: shell
hello was called
Hello howie! 
```

表面上看来，`02-2.py`代码看起来也可以很好地执行啊，可请注意，在末尾处，`hello`只是函数名称，它并不能被调用，若执行`hello()`，就会报`TypeError: 'NoneType' object is not callable`对象不能调用的错误，这是自然，因为在`decorator`中`func()`直接将传入的函数实例化了，有人会想，那如果这样改呢？

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-3.py
__author__ = 'howie'
def decorator(func):
    print("%s was called" % func.__name__)
    return func
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello() 
```

确实，这样改是可以，可有没有想过，若想在函数执行结束后加点装饰呢？这样便行不通了，可能又有人会想，若这样改呢？

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-4.py
__author__ = 'howie'
def decorator(func):
    print("%s was called" % func.__name__)
    func()
    return bye
def bye():
    print("bye~")
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello() 
```

这样写看起来，恩，怎么说呢，总有种没有意义的感觉，不如直接将在外部的函数放进`decorator`中，如下:

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-5.py
__author__ = 'howie'
def decorator(func):
    def wrapper():
      print("%s was called" % func.__name__)
      func()
      print("bye~")
    return wrapper
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello() 
```

执行：

```
outputs: shell
hello was called
Hello howie!
bye~ 
```

怎么样，输出的结果是不是符合要求，其实简单来看的话，可以这样理解`hello()==decorator(hello)()==wrapper()`，最后其实就是执行`wrapper()`函数而已，事实就是如此的简单，不妨来验证一下：

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-6.py
__author__ = 'howie'
def decorator(func):
    def wrapper():
      print("%s was called" % func.__name__)
      func()
      print("bye~")
    return wrapper
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello()
print(hello.__name__) 
```

```
outputs: shell
hello was called
Hello howie!
bye~
wrapper 
```

果然就是执行了 wrapper 函数，解决问题的同时也会出现新的问题，那便是代码中本来定义的 hello 函数岂不是被 wrapper 函数覆盖了，又该如何解决这个问题呢？这时候`functions.wraps`就可以登场了，代码如下：

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 02-7.py
__author__ = 'howie'
from functools import wraps
def decorator(func):
    @wraps(func)
    def wrapper():
      print("%s was called" % func.__name__)
      func()
      print("bye~")
    return wrapper
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello()
print(hello.__name__) 
```

执行代码：

```
outputs: shell
hello was called
Hello howie!
bye~
hello 
```

`functions.wraps`作用是不是一目了然哈~到了这一步，再看 01.py 的代码，是不是代码结构清晰明了，只不过多了个参数~

```
#!/usr/bin/env
# -*-coding:utf-8-*-
# script: 01.py
__author__ = 'howie'
from functools import wraps
def decorator(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        print("%s was called" % func.__name__)
        func(*args, **kwargs)
    return wrapper
@decorator
def hello(name="howie"):
    print("Hello %s!" % name)
hello('world') 
```

猜都猜得到执行后输出什么了。  ## 结语

只要了解装饰器原理，不管是带参数的装饰器，还是装饰器类，都是小菜一碟。

# Index

+   Introduction

+   第一部分：技巧

    +   1.初使用

    +   2.配置

    +   3.项目结构

    +   4.展示一个页面

    +   5.数据库使用

    +   6.常用的技巧

    +   7.可靠的拓展

    +   8.测试与部署

+   第二部分：源码及附录

    +   Sanic 源码阅读：基于 0.1.2

    +   附录：关于装饰器
