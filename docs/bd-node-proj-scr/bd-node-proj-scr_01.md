# Node 和 npm

# Node 介绍

有足够多的文档支持这个问题，“为什么使用 Node？”。对我来说真正有意义的是 Node 现在的状态，而不是 Node 将来的状态。毫无疑问，Rails 社区为此做出了很大贡献，但令所有这些令人惊叹的想法难以接受的是，它们被锁在 Ruby 中。尽管 Ruby 很棒，但并不是每个人都想成为 Ruby 开发人员。

我特别喜欢这句话来自*为什么我要使用 Node.js？逐例介绍*[[参考](http://www.toptal.com/nodejs/why-the-hell-would-i-use-node-js)]，作者[Tomislav Capan](http://www.toptal.com/resume/tomislav-capan)。

> ... 值得注意的是，Node.js 的创造者 Ryan Dahl 旨在创建具有推送功能的实时网站，“受到 Gmail 等应用程序的启发”。在 Node.js 中，他为开发人员提供了一种在非阻塞、事件驱动的 I/O 范式中工作的工具。

## 安装 Node

在运行任何安装程序之前，请确保您知道计算机上有什么。要查看版本，只需运行：

```
$ node --version 
```

当然，要创建和运行一个 Node 应用程序，您需要安装 Node。要安装 Node，您可以运行[它们网站上的安装程序](http://nodejs.org/)。

[安装 Node 和 npm](http://www.joyent.com/blog/installing-node-and-npm/)是一篇关于如何进行设置的绝佳文章。请注意第 4 步，其中对如何设置事物有一些非常坚定的意见。

提供了一个[gist](https://gist.github.com/579814)，其中说明了一系列安装 Node 的方法。

这篇文章确实表达了个人对使用 Homebrew 的反对意见。Brew 对我而言效果相当不错，但这是一个你可能需要自己形成的观点。

## Node 包管理器（npm）

> npm 是一个 NodeJS 包管理器。正如其名字所暗示的那样，您可以使用它来安装 Node 程序。此外，如果您在开发中使用它，那么指定和链接依赖项就会变得更容易。

[了解更多关于 npm 的信息](http://howtonode.org/introduction-to-npm)

根据您的安装过程，您可能已经安装了 NPM，也可能没有安装。要检查，请简单运行：

```
$ npm --version 
```

#### 如果您尚未安装 npm，请运行以下命令：

注意：npm 是 Node 的包管理器，因此您不能使用包管理器安装包管理器 o_O

```
$ curl http://npmjs.org/install.sh | sh 
```

## 使用 npm

现在您已经安装了 npm，所有注册的包都只是一个简单的命令远。对于基本的包安装，运行：

```
$ npm install <package> 
```

此安装方法将在一个与您的项目相关的目录（`node_modules/`）中安装包。有时候，您需要全局安装库，以便您可以从不一定需要它们作为依赖项的任何应用程序中访问其代码。

要做到这一点，您需要在安装过程中添加`-g`标志：

```
$ npm install -g <package> 
```

**注意：** 根据 Node 在您的系统上的安装方式，您可能无法访问安装全局包的权限。为了解决这个问题，只需在 npm 安装方法之前添加`sudo`命令：

```
$ sudo npm install -g <package> 
```

### 在项目中使用 npm

npm 最常见的用法是维护项目的依赖关系清单。这是通过一个 [package.json](https://www.npmjs.org/doc/json.html) 文件进行维护的。

你可以自己创建这个文件，也可以有办法生成这个文件。在任何目录中只需运行 `npm init`，CLI 就会引导你完成一系列问题，并输出类似以下的内容：

```
{
  "name": "toss-this",
  "version": "0.0.0",
  "description": "",
  "main": "index.js",
  "scripts": {
    "test": "echo \"Error: no test specified\" && exit 1"
  },
  "author": "",
  "license": "ISC"
} 
```

一旦你在你的项目中拥有这个，使用 `npm install` 来添加到它是非常容易的。只需像下面这样在命令中添加 `--save` 标志：

```
$ npm install <package> --save 
```

将 Grunt 添加到项目中会通过在 json 文件中添加一个 `dependencies` 对象来更新 `package.json` 文件：

```
{
  "name": "toss-this",
  "version": "0.0.0",
  "description": "",
  "main": "index.js",
  "scripts": {
    "test": "echo \"Error: no test specified\" && exit 1"
  },
  "author": "",
  "license": "ISC",
  "dependencies": {
    "grunt": "⁰.4.5"
  }
} 
```

此外，如果你想添加一个只用于开发而不是生产的依赖项，你可以传递 `-dev` 标志：

```
$ npm install <package> --save-dev 
```

将 Gulp 添加为开发依赖项，我们会得到以下更新的 `package.json` 文件，通过添加一个 `devDependencies` 对象：

```
{
  "name": "toss-this",
  "version": "0.0.0",
  "description": "",
  "main": "index.js",
  "scripts": {
    "test": "echo \"Error: no test specified\" && exit 1"
  },
  "author": "",
  "license": "ISC",
  "dependencies": {
    "grunt": "⁰.4.5"
  },
  "devDependencies": {
    "gulp": "³.6.2"
  }
} 
```

### 了解更多关于 npm

npm 在包管理方面是一个非常复杂的工具。查看这个 [npm cheatsheet](http://blog.nodejitsu.com/npm-cheatsheet/) 获取更深入的信息。

### 了解更多关于 package.json

`package.json` 有许多功能。要了解更多关于这一切是如何工作的，请参阅 [package.json 交互指南](http://package.json.nodejitsu.com/#)，这是一个很棒的学习工具。

## 维护依赖关系

与其他包管理器不同，npm 将这些库直接安装到项目的根目录。在没有额外步骤的情况下，这些库将很容易提交到你的版本控制中。

大多数情况下，你可能不想这样做。版本控制是通过 `package.json` 文件进行维护的，你不应该真的去进入包本身并编辑代码。

### 使用 .gitignore

要将 npm 库排除在你的版本控制之外，请将以下内容添加到你的 .gitignore 文件中。

```
node_modules 
```

### 获取依赖关系

`package.json` 文件维护着你的应用程序的依赖关系，你不会将你的依赖关系提交到你的 Git 存储库，那些克隆你的项目的人需要获取这些安装这些依赖关系。安装非常简单：

```
$ npm install 
```

执行该命令后，你应该会看到你的 CLI 正在下载互联网！
