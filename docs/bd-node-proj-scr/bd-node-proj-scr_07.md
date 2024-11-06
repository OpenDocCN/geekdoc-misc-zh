# Bower

# 用 Bower 管理所有事情

除非您生活在洞里，您应该很清楚 JavaScript 革命已经无处不在。我在 Rails 生态系统中发现的许多令人惊奇的概念现在正在爆发到 JavaScript 空间，允许更广泛地分发令人敬畏的内容。三大支柱是; Yeoman、Bower 和 Grunt。

我需要解决的问题是; 如何以最佳方式将一些库代码放到 Github 上，并使其对用户易于访问，而无需克隆项目？因为，那真的很糟糕，对吧？

## Yeoman 生成器

最初我遇到了[generator-sass-boilerplate](https://github.com/srsgores/generator-sass-boilerplate)，一个'快速搭建 Sass 样式的 Yeoman 生成器'。这是一种非常有趣的方法，用于创建一个复杂的库，并允许用户定制安装。但对于一个更简单的代码库，也许只是一些函数和混合，这就太繁琐了。

## Bower 就是答案

快进到现在。我最近看到了一些新的帖子，真正解释了 Bower 是什么以及它最擅长什么。我恍然大悟，这就是答案！

对于不了解的人来说，Bower 是前端包管理的极其简单的解决方案。

> 它提供了一个通用的、无偏见的解决方案来解决前端包管理的问题，同时通过一个 API 公开了包依赖模型，这个 API 可以被更具偏见的构建堆栈所使用。

Bower 之美在于其简洁性。Bower 有一个注册表，但这并非必需。常见命令是`bower install <package>`，其中`<package>`可以指代[大量选项](http://bower.io/#using-a-different-name-and-a-specific-version-of-a-package)，因此只需分享一些代码就变得非常简单。不错！

坚持'非常简单'的主题，您可以使用 Bower 轻松将一个仓库拉入项目中，而无需克隆它。即使没有`bower.json`文件。

例如 Stipe，一个我编写的 Compass 扩展库，根本不了解 Bower。

```
$ bower install git://github.com/Toadstool-Stipe/stipe.git 
```

在任何文件夹中运行该命令，您将获取整个仓库，没有 Github 历史记录。这本身就相当有趣。

## 使用 Bower 入门

要开始，实际上很简单。假设您的本地计算机已安装了 Node 和 npm，运行：

```
$ npm install -g bower 
```

### 安装 Bower 包

我这里不会详细说明，但 99%的情况下，您只需运行：

```
$ bower install <package> 
```

如上所述，还有其他安装选项，但主要解决方案是在仓库中有一个`bower.json`文件，并将其注册到 Bower 中。

如果您的项目中有一个`bower.json`文件，在下一节中解释，您可以在安装时添加`--save`标志，这将将库添加为项目的依赖项。太棒了。

当您分发项目时，只需运行`$ bower install`，克隆它的用户就能拉取所有外部资源。不错！

## 提交还是不提交！？

这种创建和分发资源的新系统提出了一个有趣的问题；你是否提交所有的 bower 包？在 Ruby 的世界中，Gem 实际上不是项目的一部分，而是项目的依赖项，从不提交到项目的版本控制。在这个新的 JavaScript 世界中，Node 和 Bower 包依赖项通过一个清单引用，就像 Ruby 中的 Gemfile 一样，但实际上是安装在项目目录的根目录中。

这个话题有一个[完整的讨论](http://addyosmani.com/blog/checking-in-front-end-dependencies/)。我是这样看待的，当你安装一个 Bower 库时，你是将其作为依赖项留下，还是进行修改？

选择权在你手中，双方的论点都很有说服力。在你实际分叉安装的代码的情况下，答案是相当明确的，它应该被提交到项目中，或者你需要分叉依赖项。

## 生成新的 Bower 包

再次创建一个新的 Bower 包，真的很简单。

```
$ bower init 
```

在 CLI 中，这将启动一系列问题，它的答案将填入它创建的新`bower.json`文件中。你可以尽情添加，但你真正需要的只有：

```
{
  "name": "your-project",
  "version": "0.1.0"
} 
```

就这样。你刚刚创建了你的第一个 Bower 资源库。现在前进吧！扩展你的资源、文档等等... 你的包随时准备就绪。

为了简化测试，记住`$ bower install git://github.com/ ...`的技巧？对着一个新存储库运行这个命令，看看它是如何安装的。

注意这一步以及包含的内容。在我看来，我认为 Bower 是分发较小、具体代码库的好方法。当我引入你的 Bower 包时，我真的需要你的所有文档、测试、演示资源等等吗？举个例子，我要把 Bourbon 举出来，运行：

```
$ bower install bourbon 
```

运行这个安装程序，你将获得整个存储库。我不想要整个存储库，我真正想要的只是`dist/`目录中的内容。为了解决这个问题，另一位开发者分叉了 Bourbon 并创建了一个名为 [bower-bourbon](https://github.com/hmps/bourbon) 的新存储库：

```
$ bower install bower-bourbon 
```

运行这个安装，你实际上只会得到`dist/`目录中的内容。但这些分叉可靠吗？哦，开源世界，你是一个狂野的存在。

**更新：** 有人提醒我使用 Bower 安装 Bourbon 时会拉取它的 3.2 Beta 版本，并且似乎不完全可用。本节并非意在指责“糟糕的 Bourbon”，而只是简单说明在某些情况下，使用 Bower 会得到比实际需要更多的库。

## Bower 注册

一旦准备好发布，[在 Bower 中注册它](http://bower.io/#registering-packages)。标准非常简单：

1.  确保你的存储库有`bower.json`文件

1.  你必须使用[语义版本](http://semver.org/)

1.  你的包必须在一个 Git 终端上可用，比如 Github

一旦你准备好了所有这些，用你的新包名称和 Git 终端运行这个命令：

```
$ bower register <my-package-name> <git-endpoint> 
```

注册是无痛的。一旦你对一切都有了绿灯，测试一下，运行`$ bower install <my-package-name>`

## Bower 和 Sass

Bower 和 Sass 库是一个令人惊叹的组合。Github 上到处都是小仓库，将它们制作成 Ruby Gem/Compass 扩展的复杂性太大了。你必须要么 fork，要么 clone，或者天哪，复制粘贴代码到你的项目中。什么？我们难道不是文明社会吗？

在 Ruby 世界中，开发者习惯于在一个安全的、*不可触摸的位置安装 Gems 和 Compass 扩展。新的 Gem 被添加到 Gemfile 中，我们只需在项目中引用这个库。

##### *不可触摸对许多开发者来说是一个挫败感。导入他们无法控制或无法修改的 Sass 库，实际上输出 CSS 可能非常令人沮丧。

在新的 JavaScript 世界中，库被添加到`bower.json`清单中或者直接安装，但是它不是安装在一个模糊的位置，而是安装在项目的根目录中。从安装的角度来看，这保持了事情的简单性，但这意味着我们的 Sass 导入位于相对目录中。这并不是什么大问题，但与我们习惯的方式有所不同。

那么，一个 Sass Bower 包是什么样子的呢？让我们看一个我创建的简单项目，称为 [sass-icon-fonts](https://github.com/anotheruiguy/sass-icon-fonts)。这个包简单地包含了一些 mixin，其中一个允许开发者轻松创建`@font-face`规则集，另一个是快速生成一系列图标字体规则的能力。这个小型库附带了说明和一个非常简单的 API。

现在，让我们想象一下你正在构建一个 Node 项目，你想将这个包作为资源使用，运行：

```
$ bower install sass-icon-fonts --save 
```

这将安装包并将依赖项添加到你的`bower.json`文件中。项目的根目录下是你的`sass/`目录，在其中是你的`application.scss`文件。在你的根目录下是`bower_components`目录。为了让你的`application.scss`文件访问新库，你需要导入到库的相对路径，如下所示：

```
@import "../bower_components/sass-icon-fonts/_ico-font.scss"; 
```

虽然之前的例子可以工作，虽然我觉得这是可以接受的，但我并没有觉得它真的很棒。深入研究 Grint-Sass API 我发现了 [includePaths](https://github.com/sindresorhus/grunt-sass#includepaths) 函数。这允许你设置一个导入路径以包含。

```
options: {
  includePaths: [
    './bower_components/bower-bourbon'
  ]
} 
```

现在你在你的 Grunt 文件中有了这个，你只需用简单的 Sass 导入引用库的主清单文件，就像这样：

```
@import "bourbon"; 
```

## 在你的 npm 中的 Bower

有一件事情让我稍微有点烦恼，那就是使用 Bower 时我必须运行单独的命令来初始化一个新项目。我已经在使用 npm 了，我不能把这些东西绑在一起吗？

是的，是的，你可以。在你的`package.json`文件中，简单地扩展`scripts`对象并传入`bower install`命令。这就是为什么我真的很喜欢这些东西！

```
"scripts": {
  "install": "bower install"
} 
```

现在，当你运行 `npm install` 时，这不仅会安装所有的 Node 包，还会安装你的 Bower 包。不错！

## 防火墙后的 Bower

如果你发现自己身处不允许 `git://[repo]` 协议的防火墙后，有一个解决方法。首先，我建议手动使用 `https://[repo]` 协议进行克隆，以确保这真的是问题所在。如果 `https://[repo]` 协议有效，则可能需要进行以下更新：

```
git config --global url."https://" 
```

感谢 [Stack Overflow](http://stackoverflow.com/questions/15669091/bower-install-using-only-https)!

## 摘要

当我说我想要 Bower 包管理所有东西时，我就是这个意思。现在了解了 Bower，我对简单的包管理有了全新的认识，我希望你也能有。

不再分叉、克隆、删除 `.git/` 目录，只是为了将库包含到项目中。我也在全新的光芒下看待创建 Sass 模块。不是说 Compass 扩展很困难，但 Bower 让我摆脱了多重依赖。这在许多项目中是一个真正的问题。

# Bower + Grunt + Sass

# Bower - Grunt - Sass

现在我们知道了 Bower 轻松管理我们的前端开发依赖的力量，我们需要做什么来将 Sass 代码的 Bower 包添加到我们的项目中？

## 安装 Bower

首先，让我们安装一个简单的 Bower 包作为示例：

```
$ bower install css-calc-mixin --save 
```

这样，我们现在在项目中有了代码库。

## 更新 Gruntfile.js

接下来，我们想要更新 `Gruntfile.js`，以便我们可以轻松地将库包含到我们的 Sass 文件中。如果没有这一步，我们将需要在我们的 Sass 文件中写入完整路径，这简直太烦人了。

在 Grunt-Sass API 中，我们有选项，我们需要使用的是 `includePaths`。在这里，我们可以传入一个字符串，该字符串是从根目录到 Bower 包的完整路径。

```
module.exports = function(grunt) {
  grunt.initConfig({
    sass: {
      dist: {
        files: {
          'public/stylesheets/style.css': 'sass/style.scss'
        }
      },
      options: {
        includePaths: [
          './bower_components/css-calc-mixin'
        ]
      }
    },
    watch: {
      source: {
        files: ['sass/**/*.scss', 'views/**/*.jade'],
        tasks: ['sass'],
        options: {
          livereload: true, // needed to run LiveReload
        }
      }
    }
  });

  grunt.loadNpmTasks('grunt-contrib-watch');
  grunt.loadNpmTasks('grunt-sass');
  grunt.registerTask('default', ['sass']);
}; 
```

## 更新 style.scss

要使用这个新的 Bower 包库，我们只需要使用一种 Sass 约定来导入代码。

```
@import "css-calc-mixin"; 
```

要测试这是否有效，让我们添加一点引用 Bower 库的代码。

```
.block {
  @include calc(width, 220px);
}

.block {
  @include calc(margin, 220px, 0);
}

.block {
  @include calc(width, 220px, true, 0);
}

.block {
  @include calc(width, 220px, true, 0, 50%, '+');
} 
```

回到 CLI，运行 `grunt`，我们应该看到一整天的绿灯！
