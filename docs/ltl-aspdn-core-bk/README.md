# ASP.NET Core 小型手册

# 介绍

感谢您选择《小型 ASP.NET Core 书籍》！我写了这本简短的书来帮助开发人员和对 Web 编程感兴趣的人了解 ASP.NET Core 2.0，这是一个用于构建 Web 应用程序和 API 的新框架。

《小型 ASP.NET Core 书籍》结构化为教程。你将从头到尾构建一个待办事项应用程序，并学习：

+   MVC（Model-View-Controller）模式的基础知识

+   前端代码（HTML、CSS、JavaScript）如何与后端代码配合工作

+   依赖注入是什么以及为什么它很有用

+   如何读取和写入数据库中的数据

+   如何添加登录、注册和安全性

+   如何将应用程序部署到 Web 上

别担心，你不需要了解 ASP.NET Core（或以上任何内容）就可以开始。

## 在开始之前

你将构建的应用程序的最终版本的代码可在 GitHub 上找到（[`www.github.com/nbarbettini/little-aspnetcore-todo`](https://www.github.com/nbarbettini/little-aspnetcore-todo)）。如果你想在编写自己的代码时进行比较，请随意下载。

本书本身经常更新，修复错误并添加新内容。如果你正在阅读 PDF、电子书或印刷版本，请查看官方网站（[littleasp.net/book](http://www.littleasp.net/book)）是否有更新版本可用。书的最后一页包含版本信息和更新日志。

### 以你自己的语言阅读

感谢一些出色的多语言人士，小型 ASP.NET Core 书籍已被翻译成其他语言：

**土耳其语** - [`sahinyanlik.gitbooks.io/kisa-asp-net-core-kitabi/`](https://sahinyanlik.gitbooks.io/kisa-asp-net-core-kitabi/)

**中文** - [`windsting.github.io/little-aspnetcore-book/book/`](https://windsting.github.io/little-aspnetcore-book/book/)

## 本书适合谁

如果你是编程新手，这本书将向你介绍用于构建现代 Web 应用程序的模式和概念。通过从头开始构建东西，你将学习如何构建 Web 应用程序（以及大部分组件如何配合）。虽然这本小书无法涵盖关于编程的所有内容，但它会给你一个起点，让你学习更高级的主题。

如果你已经在像 Node、Python、Ruby、Go 或 Java 这样的后端语言中编码，你会注意到许多熟悉的概念，如 MVC、视图模板和依赖注入。代码将使用 C# 编写，但与你已经了解的内容并无太大不同。

如果你是 ASP.NET MVC 开发人员，你会感到非常亲切！ASP.NET Core 添加了一些新工具，并重用（并简化）你已经了解的内容。我将在下面指出一些不同之处。

无论你之前有什么样的网络编程经验，本书都将教会你如何在 ASP.NET Core 中创建一个简单而有用的 Web 应用程序。你将学会如何使用后端和前端代码构建功能，如何与数据库交互，以及如何测试和部署应用程序到世界上。

## 什么是 ASP.NET Core？

ASP.NET Core 是由微软创建的用于构建 Web 应用程序、API 和微服务的 Web 框架。它使用常见的模式，如 MVC（模型-视图-控制器）、依赖注入和由中间件组成的请求管道。它是根据 Apache 2.0 许可证开源的，这意味着源代码是免费提供的，社区被鼓励贡献错误修复和新功能。

ASP.NET Core 运行在微软的 .NET runtime 之上，类似于 Java 虚拟机（JVM）或 Ruby 解释器。你可以使用多种语言（C#、Visual Basic、F#）编写 ASP.NET Core 应用程序。C# 是最流行的选择，也是我在本书中使用的语言。你可以在 Windows、Mac 和 Linux 上构建和运行 ASP.NET Core 应用程序。

## 为什么我们需要另一个 Web 框架？

目前已经有很多优秀的网络框架可供选择：Node/Express、Spring、Ruby on Rails、Django、Laravel 等等。ASP.NET Core 有哪些优势呢？

+   **速度。** ASP.NET Core 很快。由于 .NET 代码是编译的，它比像 JavaScript 或 Ruby 这样的解释语言执行得快得多。ASP.NET Core 还针对多线程和异步任务进行了优化。通常可以看到比使用 Node.js 编写的代码快 5-10 倍。

+   **生态系统。** ASP.NET Core 可能是新的，但 .NET 已经存在很长时间了。在 NuGet（.NET 包管理器；类似 npm、Ruby gems 或 Maven）上有数千个可用的包。已经有用于 JSON 反序列化、数据库连接器、PDF 生成或几乎任何其他你能想到的东西的包。

+   **安全。** 微软团队非常重视安全性，ASP.NET Core 是从底层构建的安全性。它自动处理诸如清理输入数据和防止跨站请求伪造（XSRF）之类的事情，因此您无需担心。你还可以通过 .NET 编译器的静态类型检查获得好处，这就像一直打开着非常谨慎的 linter。这使得很难在变量或数据块上执行你没有打算执行的操作。

## .NET Core 和 .NET Standard

在本书中，你将学习 ASP.NET Core（网络框架）。我会偶尔提到 .NET runtime（运行 .NET 代码的支持库）。

你可能也听说过 .NET Core 和 .NET Standard。命名让人感到困惑，所以这里有一个简单的解释：

**.NET Standard** 是一个平台无关的接口，定义了在 .NET 中可用的功能和 API。.NET Standard 并不代表任何实际的代码或功能，只是 API 的定义。有不同的 ".NET Standard 版本" 或级别，反映了有多少个 API 可用（或 API 表面积有多广）。例如，.NET Standard 2.0 拥有比 .NET Standard 1.5 更多的 API，而 .NET Standard 1.5 拥有比 .NET Standard 1.0 更多的 API。

**.NET Core** 是可以安装在 Windows、Mac 或 Linux 上的 .NET 运行时。它使用适用于每个操作系统的平台特定代码实现了 .NET Standard 接口中定义的 API。这就是你会在自己的计算机上安装来构建和运行 ASP.NET Core 应用程序的内容。

只是为了保险起见，**.NET Framework** 是 .NET Standard 的另一种只适用于 Windows 的实现。在 .NET Core 出现之前，这是唯一的 .NET 运行时，然后 .NET Core 开放了 .NET 到 Mac 和 Linux。ASP.NET Core 也可以在仅限于 Windows 的 .NET Framework 上运行，但我不会过多涉及这一点。

如果你对所有这些命名感到困惑，别担心！我们马上就会看到一些真正的代码。

## 给 ASP.NET 4 开发者的提示

如果你之前没有使用过 ASP.NET 的旧版本，请跳到下一章节！

ASP.NET Core 是 ASP.NET 的彻底重写，重点是现代化框架并最终将其与 System.Web、IIS 和 Windows 解耦。如果你还记得 ASP.NET 4 中的所有 OWIN/Katana 相关内容，你已经完成了一半：Katana 项目变成了 ASP.NET 5，最终改名为 ASP.NET Core。

由于 Katana 的遗留，`Startup` 类变得非常重要，不再有 `Application_Start` 或 `Global.asax`。整个管道由中间件驱动，不再存在 MVC 和 Web API 之间的分离：控制器可以简单地返回视图、状态码或数据。依赖注入已经内置，所以如果你不想安装和配置类似 StructureMap 或 Ninject 的容器，也无需这样做。整个框架都经过了速度和运行时效率的优化。

好了，够介绍的了。让我们开始学习 ASP.NET Core 吧！
