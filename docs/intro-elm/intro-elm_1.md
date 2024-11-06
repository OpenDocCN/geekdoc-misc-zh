# 安装

> **注意：** 如果你不想安装，可以在本指南中使用[在线编辑器](http://elm-lang.org/try)和[在线 REPL](http://elmrepl.cuberoot.in/)跟着学习。

# 安装

+   Mac — [安装程序](http://install.elm-lang.org/Elm-Platform-0.18.pkg)

+   Windows — [安装程序](http://install.elm-lang.org/Elm-Platform-0.18.exe)

+   任何地方 — [npm 安装程序](https://www.npmjs.com/package/elm) 或[从源代码构建](https://github.com/elm-lang/elm-platform)

通过任何这些途径安装后，你将拥有以下命令行工具：

+   `elm-repl` — 与 Elm 表达式互动

+   `elm-reactor` — 快速启动项目

+   `elm-make` — 直接编译 Elm 代码

+   `elm-package` — 下载包

我们将在设置好你的编辑器后立即详细介绍它们的工作原理！

> **故障排除：** 学习*任何*东西的最快方法是与 Elm 社区的其他人交流。我们友好且乐意帮助！所以，如果在安装过程中遇到困难或遇到奇怪的问题，请访问[Elm Slack](http://elmlang.herokuapp.com/)并询问。事实上，如果在学习或使用 Elm 的任何阶段遇到令人困惑的问题，请随时向我们询问。这样可以节省你几个小时。就这样！

## 配置你的编辑器

使用 Elm 时最好有一个代码编辑器来帮助你。以下至少有以下编辑器的 Elm 插件：

+   [Atom](https://atom.io/packages/language-elm)

+   [括号](https://github.com/lepinay/elm-brackets)

+   [Emacs](https://github.com/jcollard/elm-mode)

+   [IntelliJ](https://github.com/durkiewicz/elm-plugin)

+   [Light Table](https://github.com/rundis/elm-light)

+   [Sublime Text](https://packagecontrol.io/packages/Elm%20Language%20Support)

+   [Vim](https://github.com/ElmCast/elm-vim)

+   [VS Code](https://github.com/sbrink/vscode-elm)

如果你根本没有编辑器，[Sublime Text](https://www.sublimetext.com/)是一个很好的开始！

你可能还想尝试一下[elm-format](https://github.com/avh4/elm-format)，它可以让你的代码更漂亮！

## 命令行工具

所以我们安装了 Elm，它给了我们`elm-repl`、`elm-reactor`、`elm-make`和`elm-package`。但它们究竟是做什么的呢？

### elm-repl

[`elm-repl`](https://github.com/elm-lang/elm-repl) 让你可以玩弄简单的 Elm 表达式。

```
$ elm-repl
---- elm-repl 0.18.0 -----------------------------------------------------------
 :help for help, :exit to exit, more at <https://github.com/elm-lang/elm-repl>
--------------------------------------------------------------------------------
> 1 / 2
0.5 : Float
> List.length [1,2,3,4]
4 : Int
> String.reverse "stressed"
"desserts" : String
> :exit
$ 
```

我们将在接下来的“核心语言”部分使用`elm-repl`，你可以在[这里](https://github.com/elm-lang/elm-repl/blob/master/README.md)详细了解它的工作原理。

> **注意：** `elm-repl` 通过将代码编译为 JavaScript 来工作，因此请确保已安装[Node.js](http://nodejs.org/)。我们使用它来评估代码。

### elm-reactor

[`elm-reactor`](https://github.com/elm-lang/elm-reactor) 帮助你构建 Elm 项目，而不用���过纠结于命令行。只需在项目的根目录运行它，就像这样：

```
git clone https://github.com/evancz/elm-architecture-tutorial.git
cd elm-architecture-tutorial
elm-reactor 
```

这将在[`http://localhost:8000`](http://localhost:8000)启动一个服务器。你可以导航到任何 Elm 文件并查看其内容。尝试查看`examples/01-button.elm`。

**值得注意的标志：**

+   `--port` 让你选择除了端口 8000 之外的东西。因此，你可以说`elm-reactor --port=8123`来使事情在`http://localhost:8123`上运行。

+   `--address` 让你用其他地址替换`localhost`。例如，如果你想通过本地网络在移动设备上尝试 Elm 程序，你可能想使用`elm-reactor --address=0.0.0.0`。

## elm-make

[`elm-make`](https://github.com/elm-lang/elm-make) 构建 Elm 项目。它可以将 Elm 代码编译为 HTML 或 JavaScript。这是编译 Elm 代码的最常用方法，所以如果你的项目对`elm-reactor`来说太复杂了，你就会想直接开始使用`elm-make`。

假设你想要将`Main.elm`编译为一个名为`main.html`的 HTML 文件。你会运行这个命令：

```
elm-make Main.elm --output=main.html 
```

**值得注意的标志：**

+   `--warn` 输出警告以提高代码质量。

### elm-package

[`elm-package`](https://github.com/elm-lang/elm-package) 从我们的[包目录](http://package.elm-lang.org/)下载并发布包。当社区成员以[友好的方式](http://package.elm-lang.org/help/design-guidelines)解决问题时，他们会在包目录中分享他们的代码供任何人使用！

假设你想要使用[`elm-lang/http`](http://package.elm-lang.org/packages/elm-lang/http/latest)和[`NoRedInk/elm-decode-pipeline`](http://package.elm-lang.org/packages/NoRedInk/elm-decode-pipeline/latest)来向服务器发出 HTTP 请求并将结果 JSON 转换为 Elm 值。你会说：

```
elm-package install elm-lang/http
elm-package install NoRedInk/elm-decode-pipeline 
```

这将把依赖项添加到描述你的项目的`elm-package.json`文件中。（如果你还没有一个的话，会创建一个！）关于这一切的更多信息[在这里](https://github.com/elm-lang/elm-package)！

**值得注意的命令：**

+   `install`：在`elm-package.json`中安装依赖项

+   `publish`：将你的库发布到 Elm Package Catalog

+   `bump`：根据 API 更改来增加版本号。

+   `diff`：获取两个 API 之间的差异
