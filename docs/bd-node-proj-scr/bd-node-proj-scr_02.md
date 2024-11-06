# Express

# Express，Node 框架

[Expressjs](http://expressjs.com/) 是 Node.js 应用程序的 Web 应用程序框架。

> Express 是一个简洁灵活的 Node.js Web 应用程序框架，提供了一套强大的功能，用于构建单页、多页和混合 Web 应用程序。

它拥有丰富的 [API](http://expressjs.com/4x/api.html)，而且速度快得要命！

Express 以不追随 Rails 为框架而闻名，而更多地是借鉴了另一个名为 [Sinatra](http://www.sinatrarb.com/) 的 Ruby 框架。概念很简单，框架为您提供了足够的东西，让您尽快启动并运行，而且不会妨碍您。

大多数情况下，Express 仍��符合这一说法。

在这个研讨会中，我们将使用 Express 作为核心工具，通过服务器、路由支持、错误页面、日志记录器等来快速启动 Web 应用程序。

## 安装 Express

使用 npm 安装 Express 真的很容易。请记住，Express 有两个部分，一个是运行它的库，另一个是一个很棒的生成器。

要安装 Express：

```
$ npm install express -g 
```

要安装生成器：

```
$ npm install express-generator -g 
```

## 生成器版本

最近发布了 Express 4.0，有些人对此并不熟悉。因此，npm 有一种指定要安装的生成器版本的方法。

```
$ npm install -g express-generator@3 
```

# 创建一个新应用程序

# 创建一个新的 Express 应用程序

在这一点上，您应该能够继续创建一个应用程序。在这个示例中，我们将使用 Express 框架创建一个 Node.js 应用程序。

```
$ express <your-new-app> 
```

运行此命令（以 `demo-app` 为例），您应该看到以下内容：

```
 create : demo-app
 create : demo-app/package.json
 create : demo-app/app.js
 create : demo-app/public
 create : demo-app/public/javascripts
 create : demo-app/public/images
 create : demo-app/public/stylesheets
 create : demo-app/public/stylesheets/style.css
 create : demo-app/routes
 create : demo-app/routes/index.js
 create : demo-app/routes/users.js
 create : demo-app/views
 create : demo-app/views/index.jade
 create : demo-app/views/layout.jade
 create : demo-app/views/error.jade
 create : demo-app/bin
 create : demo-app/bin/www

 install dependencies:
   $ cd demo-app && npm install

 run the app:
   $ DEBUG=my-application ./bin/www 
```

哇！Express 处理了大部分工作。现在，我们按照计算机的指示，切换到应用程序目录并运行 `npm install`。

## 应用程序中有什么？

在这一点上，您应该能够执行 `ls` 命令并查看为您创建的新结构。

```
app.js    node_modules/ public/   views/
bin/    package.json  routes/ 
```

#### app.js

这是您应用程序的逻辑起点。让我们谈谈其中的一些内容：

对于这种类型的应用程序，我们不需要以下行：

```
var user = require('./routes/user');

app.get('/users', user.list); 
```

设置视图文件所在目录的路径：

```
app.set('views', path.join(__dirname, 'views')); 
```

设置静态资产目录的路径：

```
app.use(express.static(path.join(__dirname, 'public'))); 
```

设置应用程序的根路由：

```
app.use('/', routes); 
```

#### node_modules/

这是您所有 npm 包将驻留的目录。

#### public/

用于存放所有静态资产（如图像、JavaScript、CSS、字体等）的目录...

#### views/

这是您的布局和视图 Jade 文件的存放位置。

#### bin/

这里只有一个文件，`www`，这是激活 Node 服务器的文件。

#### package.json

项目描述、脚本管理器和应用程序清单。注意以下对象：

```
"scripts": {
  "start": "node ./bin/www"
}, 
```

这是允许您为应用程序运行 `npm start` 的代码。

#### routes/

这是您将为应用程序构建 RESTful 路由的目录。基本安装应该有两个文件，`index.js` 和 `users.js`。

# 路由

# 路由乐趣

`app.VERB()` 方法在 Express 中提供路由功能，其中**VERB**是 HTTP 动词之一，比如`app.post()`。可以提供多个回调函数，所有回调函数都会被平等对待，并且表现得像中间件一样，唯一的例外是这些回调函数可以调用`next('route')`来绕过剩余的路由回调函数。这种机制可以用于在路由上执行前提条件，然后在没有继续匹配路由的理由时将控制权传递给后续路由。

以下代码片段说明了可能的最简单的路由定义。Express 将路径字符串转换为正则表达式，内部用于匹配传入的请求。查询字符串在执行这些匹配时**不**被考虑，例如`GET /`将匹配以下路由，`GET /?name=tobi`也将匹配。

[来源](http://expressjs.com/4x/api.html#app.VERB)

```
app.VERB(path, [callback...], callback) 
```

让我们开始设置一些路由。在`app.js`文件中，以下行是如何组合在一起的：

```
var routes = require('./routes/index'); 
```

这里发生了什么？基本上，Express 将`routes`的`var`设置为需要`./routes.index`的路径和文件。

然后使用这个变量来设置应用程序的根路径

```
app.use('/', routes); 
```

我们还可以使用`res.send()`，无论我们放入其中的内容都将直接发送到浏览器。例如：

```
router.get('/foo', function(req, res){
  res.send('hello world');
}); 
```

使用`res.send()`，我们可以做一些有趣的事情，比如发送 JSON 对象。

```
router.get('/foo', function(req, res){
  res.send({'name':'Bob Goldcat', 'age': '41'})
}); 
```

这个方法允许我们在需要时将所有路由保留在`index.js`文件中。有更好的方法来解决更复杂的路由问题，但在这个研讨会的范围内，这是很好的。

## `index.js`文件中有什么？

查看我们的`index.js`文件，你应该看到以下内容：

```
var express = require('express');
var router = express.Router();

/* GET home page. */
router.get('/', function(req, res) {
  res.render('index', { title: 'Express' });
});

module.exports = router; 
```

##### router.get

这是将'get' URL 路径为`/`的函数。然后我们需要创建一个函数，该函数将进行`req`（请求）和`res`（响应）。这里还有一个关于链式事件的`next`的概念，但在这个例子中没有显示。

##### 什么是 module.exports？

这是实际作为 require 调用结果返回的对象。这是 Node 的一个特性，更多信息请参考[nodejs.org/api](http://nodejs.org/api/modules.html#modules_module_exports)。

## 建立一个新的路由

查看语法模式，如果我们想要向应用程序添加一个新的路由，我们可以简单地做如下操作：

```
router.get('/app', function(req, res) {
  res.render('app', { title: 'Express' });
}); 
```

请记住，URL 的值`/app`不需要与文件本身的值相同。如果视图的名称是`foo.jade`，我们可以这样做：

```
router.get('/app', function(req, res) {
  res.render('foo', { title: 'Express' });
}); 
```

## 这是一个路由？这是一个控制器？

这里有趣的地方是路由函数包含逻辑。在路由内���有一个`res.render`函数：

```
res.render('foo', { title: 'Express' }); 
```

在视图模板中，我们看到了这个：

```
h1= title
p Welcome to #{title} 
```

这是我们可以从'controller/route'中提取数据并在视图中显示的两个示例。在这个例子中，我们得到了以下 HTML 输出：

```
<h1>Express</h1>
<p>Welcome to Express</p> 
```

所有这些似乎是关注点的混合，因为路由也可能包含控制器信息？这是真的，社区中有一个运动，将目录的名称从`routes`更改为`controllers`。

一个很好的例子可以在[Holowaychuk](https://github.com/visionmedia/express/tree/master/examples/mvc)的 Express MVC 示例仓库中看到。

但为了这个研讨会的完整性和一致性，我们将保持当前的惯例。

# 404 错误

# 404 错误？

对于你，Express 已经处理了错误。在 `app.js` 文件中，有以下内容：

```
/// catch 404 and forwarding to error handler
app.use(function(req, res, next) {
    var err = new Error('Not Found');
    err.status = 404;
    next(err);
}); 
```

然后在 `views/` 目录中，有一个 `errors.jade` 文件。

```
extends layout

block content
  h1= message
  h2= error.status
  pre #{error.stack} 
```

简单。如果你想自定义你的 404 页面，只需编辑这个视图。
