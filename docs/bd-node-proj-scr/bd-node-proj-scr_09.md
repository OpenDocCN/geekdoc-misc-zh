# Heroku

# Heroku

以下是快速设置一个带有 Express 的 Node.js 应用程序并部署到 Heroku 所需的基本步骤。

### 步骤 1 - Heroku 帐户

确保你已经设置好了 Heroku 帐户。

### 步骤 2 - 安装 Heroku Toolbelt

下载并安装适用于你的操作系统的工具包

##### OSX

[`toolbelt.heroku.com/osx`](https://toolbelt.heroku.com/osx)

#### Windows

[`toolbelt.heroku.com/windows`](https://toolbelt.heroku.com/windows)

#### Linux

```
$ wget -qO- https://toolbelt.heroku.com/install-ubuntu.sh | sh 
```

### 步骤 3 - 登录你的帐户

安装完工具包后，你应该能够访问你的帐户

```
$ heroku login
Enter your Heroku credentials.
Email: adam@example.com
Password:
Could not find an existing public key.
Would you like to generate one? [Yn]
Generating new SSH public key.
Uploading ssh public key /Users/adam/.ssh/id_rsa.pub 
```

就是这样。通过这些步骤，你就准备好部署代码了！

# 部署代码

# 部署你的第一个应用程序

此时，你应该有一个在本地计算机上运行的应用程序。以下步骤概述了你需要进行的更新以部署代码。

## 更新 package.json

在这一步中，我们需要向`package.json`文件中添加一些代码，以便我们可以从远程服务器运行应用程序。

此刻，文件很可能看起来像这样：

```
{
  "name": "application-name",
  "version": "0.0.1",
  "private": true,
  "scripts": {
    "start": "node ./bin/www"
  },
  "dependencies": {
    "express": "~4.0.0",
    "static-favicon": "~1.0.0",
    "morgan": "~1.0.0",
    "cookie-parser": "~1.0.1",
    "body-parser": "~1.0.0",
    "debug": "~0.7.4",
    "jade": "~1.3.0"
  }
} 
```

在`dependencies": { ... }`对象的末尾，你需要添加一个逗号`,`以便我们可以添加更多代码。首先让我们添加`main`关键字：

```
"main": "app.js", 
```

注意到末尾的逗号了吗？这是因为我们将添加更多内容。之后，添加`engines`对象和我们运行此应用程序所需的特定引擎：

```
"engines": {
  "node": "0.10.26",
  "npm": "1.4.3"
} 
```

你应该有类似以下的东西：

```
{
  "name": "application-name",
  "version": "0.0.1",
  "private": true,
  "scripts": {
    "start": "node ./bin/www"
  },
  "dependencies": {
    "express": "~4.0.0",
    "static-favicon": "~1.0.0",
    "morgan": "~1.0.0",
    "cookie-parser": "~1.0.1",
    "body-parser": "~1.0.0",
    "debug": "~0.7.4",
    "jade": "~1.3.0"
  },
  "main": "app.js",
  "engines": {
    "node": "0.10.26",
    "npm": "1.4.3"
  }
} 
```

### 不要忘记 Grunt + Bower

如果此时你的`dependenciess`对象中没有任何 Grunt 包或 Bower 包，我们需要将它们添加进去。

你可以手动将它们添加到`package.json`文件中，或者运行：

```
$ npm install --save grunt
$ npm install --save grunt-sass
$ npm install --save bower 
```

你可能没有的一件事是部署服务器运行 Grunt 任务的能力。为此，我们需要 Grunt-CLI。

```
$ npm install --save grunt-cli 
```

此刻，你应该看起来相当不错。

### 安装后的说明

当我们将代码部署到 Heroku 时，我们必须告诉它运行一些命令，基本上安装 Bower 包并运行 Grunt 任务。为此，我们需要在`package.json`文件的`scripts`对象中添加说明。

在`"start": "node ./bin/www"`的下面，添加：

```
"postinstall": "./node_modules/.bin/bower install && ./node_modules/.bin/grunt" 
```

现在，我们已经为 Heroku 提供了安装包和运行脚本所需的一切。

## 添加 Procfile

这是 Heroku 启动应用程序所需的文件。

```
$ touch Procfile 
```

添加以下代码：

```
web: npm start 
```

Heroku 将使用此代码来启动应用程序。

## 将其设置为 Git 存储库

在创建 Heroku 服务器之前，重要的是将其设置为 git 存储库。**等等！**在进行 Git 操作之前，我们需要做一些事情。

此时，你的存储库中应该有一个`.gitignore`文件。打开它并确保你忽略所有的`node_modules`，所有的`bower_components`以及`/stylesheets/*.css`范围内的任何内容。

```
node_modules
public/stylesheets/*.css
bower_components 
```

太好了。现在你可以`git init`你的存储库。

```
$ git add .
$ git commit -m "initial commit" 
```

此时不需要将其设置为 Github 存储库，但如果你将其制作成一个真正的应用程序，可能会想要这样做。

## 部署代码

这里相当困难。确保按照指令具体执行：

```
$ heroku create <your-app-name>
$ git push heroku master 
```

## 庆祝

如果一切顺利，你应该看到这样的返回：

```
http://<your-new-app>.herokuapp.com/ deployed to Heroku 
```

前往该网址并**庆祝**！！！
