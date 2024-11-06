# MVC 基础知识

# MVC 基础知识

在本章中，你将探索 ASP.NET Core 中的 MVC 系统。**MVC**（模型-视图-控制器）是一种用于构建 Web 应用程序的模式，几乎在每个 Web 框架中都有使用（Ruby on Rails 和 Express 是流行的示例），以及前端 JavaScript 框架（如 Angular）。iOS 和 Android 上的移动应用程序也使用 MVC 的变体。

正如其名称所示，MVC 有三个组件：模型、视图和控制器。**控制器**处理来自客户端或 Web 浏览器的传入请求，并决定运行哪些代码。**视图**是模板（通常是 HTML 加上一些模板语言，如 Handlebars、Pug 或 Razor），其中添加了数据，然后显示给用户。**模型**保存添加到视图中的数据，或用户输入的数据。

MVC 代码的常见模式是：

+   控制器接收请求并在数据库中查找一些信息

+   控制器使用信息创建模型，并将其附加到视图

+   视图被呈现并显示在用户的浏览器中

+   用户点击按钮或提交表单，这将发送一个新的请求给控制器

如果你在其他语言中使用过 MVC，那么在 ASP.NET Core MVC 中你会感到非常亲切。如果你对 MVC 还不熟悉，本章将教你基础知识，并帮助你入门。

## 你将构建什么

MVC 的“Hello World”练习是构建一个待办事项列表应用程序。这是一个很棒的项目，因为它的规模小而简单，但涵盖了 MVC 的每个部分，并涵盖了你在更大的应用程序中可能使用的许多概念。

在本书中，你将构建一个待办事项应用程序，允许用户将项目添加到他们的待办事项列表中，并在完成后将其标记为已完成。你将使用 ASP.NET Core、C# 和 MVC 模式构建服务器（后端）。你将在视图（也称为前端）中使用 HTML、CSS 和 JavaScript。

如果你还没有使用 `dotnet new mvc` 创建一个新的 ASP.NET Core 项目，请按照前一章的步骤操作。你应该能够构建并运行项目，并看到默认的欢迎屏幕。

# 创建一个控制器

## 创建控制器

项目的 Controllers 文件夹中已经有几个控制器，包括 `HomeController`，该控制器在访问 `http://localhost:5000` 时呈现默认的欢迎屏幕。现在你可以忽略这些控制器。

为待办事项列表功能创建一个名为 `TodoController` 的新控制器，并添加以下代码：

**`Controllers/TodoController.cs`**

```
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.AspNetCore.Mvc;

namespace AspNetCoreTodo.Controllers
{
    public class TodoController : Controller
    {
        // Actions go here
    }
} 
```

由控制器处理的路由称为**操作**，并由控制器类中的方法表示。例如，`HomeController` 包括三个操作方法（`Index`、`About` 和 `Contact`），这些方法由 ASP.NET Core 映射到以下路由 URL：

```
localhost:5000/Home         -> Index()
localhost:5000/Home/About   -> About()
localhost:5000/Home/Contact -> Contact() 
```

ASP.NET Core 使用了一些约定（常见模式），比如`FooController`的模式变成了`/Foo`，并且`Index`动作名称可以省略 URL。你可以根据需要自定义此行为，但目前我们将遵循默认约定。

向`TodoController`添加一个名为`Index`的新动作，替换掉`// Actions go here`的注释：

```
public class TodoController : Controller
{
    public IActionResult Index() {
        // Get to-do items from database

        // Put items into a model

        // Render view using the model
    }
} 
```

动作方法可以返回视图、JSON 数据，或者 HTTP 状态码，比如`200 OK`或`404 Not Found`。`IActionResult`返回类型使你能够从动作中返回其中任何一个。

尽可能将控制器保持轻量级是一种最佳实践。在这种情况下，控制器应该只负责从数据库中获取待办事项，将这些项目放入视图可以理解的模型中，并将视图发送回用户的浏览器。

在你能够编写控制器代码的其余部分之前，你需要创建一个模型和一个视图。

# 创建模型

## 创建模型

需要创建两个单独的模型类：一个模型表示存储在数据库中的待办事项（有时称为**实体**），另一个模型将与视图结合（MVC 中的**V**），并发送回用户的浏览器。因为两者都可以称为“模型”，所以我将后者称为*视图模型*。

首先，在 Models 目录中创建一个名为`TodoItem`的类：

**`Models/TodoItem.cs`**

```
using System;

namespace AspNetCoreTodo.Models
{
    public class TodoItem
    {
        public Guid Id { get; set; }

        public bool IsDone { get; set; }

        public string Title { get; set; }

        public DateTimeOffset? DueAt { get; set; }
    }
} 
```

此类定义了数据库需要为每个待办事项存储的内容：一个 ID、一个标题或名称、项目是否完成，以及截止日期是什么。每一行定义了类的一个属性：

+   **Id**属性是一个全局唯一标识符（guid）。Guids（或 GUIDs）是一长串字母和数字，比如`43ec09f2-7f70-4f4b-9559-65011d5781bb`。因为 guid 是随机生成的，极不可能意外重复，所以它们通常用作唯一标识符。你也可以使用数字（整数）作为数据库实体 ID，但需要配置数据库，以便在向数据库添加新行时始终递增数字。Guids 是随机生成的，所以你不必担心自动递增。

+   **已完成**（IsDone）属性是一个布尔值（true/false）。默认情况下，对于所有新项目，它将是`false`。稍后你会编写代码，在用户在视图中点击项目的复选框时，将此属性切换为`true`。

+   **标题**（Title）属性是一个字符串。这将保存待办事项的名称或描述。

+   **DueAt**属性是一个`DateTimeOffset`，它是 C# 类型，用于存储带有时区偏移量的日期/时间戳。将日期、时间和时区偏移量一起存储使得在不同时区的系统上准确渲染日期变得很容易。

注意`DateTimeOffset`类型后面的`?`问号？那标记了 DueAt 属性为*可空*或可选。如果不包含`?`，则每个待办事项都需要有到期日期。Id 和 IsDone 属性未标记为可空，因此它们是必需的并且始终具有值（或默认值）。

> C#中的字符串始终可空，因此不需要将 Title 属性标记为可空。C#字符串可以为 null、空或包含文本。

每个属性后面跟着`get; set;`，这是一种简写方式，表示属性是可读/可写的（或更确切地说，它具有 getter 和 setter 方法）。

在这一点上，底层数据库技术是什么并不重要。它可以是 SQL Server，MySQL，MongoDB，Redis 或更奇特的东西。该模型定义了在 C#中数据库行或条目的外观，因此您无需担心代码中的底层数据库问题。这种简单的模型风格有时称为“普通的 C#对象”或 POCO。

### 视图模型

通常，您存储在数据库中的模型（实体）与您要在 MVC 中使用的模型（视图模型）相似但不完全相同。在这种情况下，`TodoItem`模型表示数据库中的单个项目，但视图可能需要显示两个，十个或一百个待办事项（取决于用户拖延的程度）。

因此，视图模型应该是一个单独的类，其中包含一个`TodoItem`数组：

**`Models/TodoViewModel.cs`**

```
using System.Collections.Generic;

namespace AspNetCoreTodo.Models
{
    public class TodoViewModel
    {
        public IEnumerable<TodoItem> Items { get; set; }
    }
} 
```

`IEnumerable<>`是 C#的一种高级方式，表示`Items`属性包含零个、一个或多个`TodoItem`。（从技术上讲，它不完全是数组，而是任何可以枚举或迭代的序列的类似数组的接口。）

> `IEnumerable<>`接口存在于`System.Collections.Generic`命名空间中，因此您需要在文件顶部添加一个`using System.Collections.Generic`语句。

现在你有了一些模型，是时候创建一个视图，它将采用`TodoViewModel`并渲染正确的 HTML 以向用户显示他们的待办事项列表。

# 创建一个视图

## 创建一个视图

ASP.NET Core 中的视图使用 Razor 模板语言构建，该语言结合了 HTML 和 C#代码。（如果你曾经使用 Jade/Pug 或 Handlebars Mustaches 编写过页面，或者使用 Ruby on Rails 中的 ERB，或者 Java 中的 Thymeleaf，你可能已经有了基本的思路。）

大多数视图代码只是 HTML，偶尔会添加 C#语句以从视图模型中提取数据并将其转换为文本或 HTML。C#语句以`@`符号为前缀。

`TodoController`的`Index`操作呈现的视图需要将视图模型中的数据（待办事项数组）显示为用户的漂亮表格。按照惯例，视图放置在`Views`目录中，子目录对应于控制器名称。视图的文件名是动作的名称，带有`.cshtml`扩展名。

**`Views/Todo/Index.cshtml`**

```
@model TodoViewModel

@{
    ViewData["Title"] = "Manage your todo list";
}

<div class="panel panel-default todo-panel">
  <div class="panel-heading">@ViewData["Title"]</div>

  <table class="table table-hover">
      <thead>
          <tr>
              <td>&#x2714;</td>
              <td>Item</td>
              <td>Due</td>
          </tr>
      </thead>

      @foreach (var item in Model.Items)
      {
          <tr>
              <td>
                <input type="checkbox" name="@item.Id" value="true" class="done-checkbox">
              </td>
              <td>@item.Title</td>
              <td>@item.DueAt</td>
          </tr>
      }
  </table>

  <div class="panel-footer add-item-form">
    <form>
        <div id="add-item-error" class="text-danger"></div>
        <label for="add-item-title">Add a new item:</label>
        <input id="add-item-title">
        <button type="button" id="add-item-button">Add</button>
    </form>
  </div>
</div> 
```

在文件的最顶部，`@model` 指令告诉 Razor 预期此视图绑定到哪个模型。通过 `Model` 属性访问模型。

假设 `Model.Items` 中有任何待办事项，`foreach` 语句将遍历每个待办事项并渲染一个包含该项目名称和到期日期的表行（`<tr>` 元素）。还渲染了一个复选框，其中包含项目的 ID，稍后你将使用它来标记项目为已完成。

### 布局文件

你可能想知道其他 HTML 在哪里：页面的 `<body>` 标签、页眉和页脚呢？ASP.NET Core 使用布局视图定义了其余视图呈现在其中的基本结构。它存储在 `Views/Shared/_Layout.cshtml` 中。

默认的 ASP.NET Core 模板在这个布局文件中包含了 Bootstrap 和 jQuery，所以你可以快速创建一个 Web 应用程序。当然，你也可以使用你自己的 CSS 和 JavaScript 库。

### 自定义样式表

暂时只需将这些 CSS 样式规则添加到 `site.css` 文件的底部：

**`wwwroot/css/site.css`**

```
div.todo-panel {
  margin-top: 15px;
}

table tr.done {
  text-decoration: line-through;
  color: #888;
} 
```

你可以使用这样的 CSS 规则来完全自定义你的页面的外观和感觉。

ASP.NET Core 和 Razor 可以做得更多，比如部分视图和服务器呈现的视图组件，但是现在你只需要一个简单的布局和视图。官方的 ASP.NET Core 文档（位于 `https://docs.asp.net`）包含了许多示例，如果你想了解更多的话。

# 添加一个服务类

## 添加一个服务类

你已经创建了一个模型、一个视图和一个控制器。在你在控制器中使用模型和视图之前，你还需要编写代码来从数据库获取用户的待办事项。

你可以直接在控制器中编写这个数据库代码，但是最好的做法是将所有的数据库代码放在一个名为**服务**的单独类中。这有助于保持控制器尽可能简单，并使后续测试和更改数据库代码变得更容易。

> 将你的应用逻辑分为一个处理数据库访问的层和另一个处理呈现视图的层有时被称为分层、三层或多层架构。

.NET 和 C# 包括**接口**的概念，接口的定义是对象的方法和属性的定义与实际包含该方法和属性的类分开的。接口使得保持你的类解耦并且易于测试，就像你在这里（以及后面的*自动化测试*章节中）所看到的那样。

首先，创建一个代表可以与数据库中的待办事项进行交互的服务的接口。按照惯例，接口以"I"为前缀。在 Services 目录中创建一个新文件：

**`Services/ITodoItemService.cs`**

```
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using AspNetCoreTodo.Models;

namespace AspNetCoreTodo.Services
{
    public interface ITodoItemService
    {
        Task<IEnumerable<TodoItem>> GetIncompleteItemsAsync();
    }
} 
```

注意这个文件的命名空间是`AspNetCoreTodo.Services`。命名空间是组织.NET 代码文件的一种方式，按照文件所在的目录来命名空间是一种习惯做法（对于`Services`目录中的文件来说，命名空间就是`AspNetCoreTodo.Services`，依此类推）。

因为这个文件（在`AspNetCoreTodo.Services`命名空间中）引用了`TodoItem`类（在`AspNetCoreTodo.Models`命名空间中），所以它需要在文件顶部包含一个`using`语句来导入该命名空间。没有`using`语句，你会看到一个错误，如下所示：

```
The type or namespace name 'TodoItem' could not be found (are you missing a using directive or an assembly reference?) 
```

由于这是一个接口，这里实际上没有任何代码，只有`GetIncompleteItemsAsync`方法的定义（或**方法签名**）。这个方法不需要参数，并返回一个`Task<IEnumerable<TodoItem>>`。

> 如果这个语法看起来令人困惑，想一想：“包含一个 TodoItems 列表的 Task”。

`Task`类型类似于将来或承诺，它在这里被使用，因为这个方法将是**异步**的。换句话说，该方法可能不能立即返回待办事项列表，因为它需要先访问数据库。（稍后详细讨论。）

现在接口已经定义好了，你可以开始创建真正的服务类了。我将在*使用数据库*章节深入讲解数据库代码，但现在你只需模拟一下，返回硬编码的值即可：

**`Services/FakeTodoItemService.cs`**

```
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using AspNetCoreTodo.Models;

namespace AspNetCoreTodo.Services
{
    public class FakeTodoItemService : ITodoItemService
    {
        public Task<IEnumerable<TodoItem>> GetIncompleteItemsAsync()
        {
            // Return an array of TodoItems
            IEnumerable<TodoItem> items = new[]
            {
                new TodoItem
                {
                    Title = "Learn ASP.NET Core",
                    DueAt = DateTimeOffset.Now.AddDays(1)
                },
                new TodoItem
                {
                    Title = "Build awesome apps",
                    DueAt = DateTimeOffset.Now.AddDays(2)
                }
            };

            return Task.FromResult(items);
        }
    }
} 
```

这个`FakeTodoItemService`实现了`ITodoItemService`接口，但总是返回两个`TodoItem`的相同数组。你将使用这个来测试控制器和视图，然后在*使用数据库*中添加真正的数据库代码。

# 使用依赖注入

## 使用依赖注入

回到`TodoController`，添加一些代码来处理`ITodoItemService`：

```
public class TodoController : Controller
{
    private readonly ITodoItemService _todoItemService;

    public TodoController(ITodoItemService todoItemService) {
        _todoItemService = todoItemService;
    }

    public IActionResult Index() {
        // Get to-do items from database

        // Put items into a model

        // Pass the view to a model and render
    }
} 
```

由于`ITodoItemService`位于`Services`命名空间中，你还需要在顶部添加一个`using`语句：

```
using AspNetCoreTodo.Services; 
```

类的第一行声明了一个私有变量来保存对`ITodoItemService`的引用。这个变量让你稍后可以从`Index`动作方法中使用该服务（稍后你会看到如何使用）。

`public TodoController(ITodoItemService todoItemService)`这行代码定义了类的一个**构造函数**。构造函数是一个特殊的方法，当你想要创建一个类的新实例时（在本例中是`TodoController`类），就会调用这个方法。通过在构造函数中添加一个`ITodoItemService`参数，你声明了要创建`TodoController`，你需要提供一个与`ITodoItemService`接口匹配的对象。

> 接口很棒，因为它们有助于解耦（分离）应用程序的逻辑。由于控制器依赖于`ITodoItemService`接口，而不是任何*特定*的服务类，因此它不知道也不关心实际给定的是哪个类。它可以是`FakeTodoItemService`，一个连接到实时数据库的不同服务，或其他任何东西！只要它符合接口，控制器就不在乎。这使得分开测试应用程序的各个部分变得非常容易。（我将在*自动化测试*章节中更详细地介绍测试。）

现在，您可以在操作方法中使用`ITodoItemService`（通过您声明的私有变量）从服务层获取待办事项：

```
public IActionResult Index() {
    var todoItems = await _todoItemService.GetIncompleteItemsAsync();

    // ...
} 
```

记得`GetIncompleteItemsAsync`方法返回了一个`Task<IEnumerable<TodoItem>>`吗？返回一个`Task`意味着该方法不一定会立即有结果，但您可以使用`await`关键字确保您的代码在继续执行之前等待结果准备就绪。

当您的代码调用数据库或 API 服务时，`Task`模式很常见，因为它在数据库（或网络）响应之前无法返回真正的结果。如果您在 JavaScript 或其他语言中使用过 promises 或回调，`Task`是相同的概念：承诺将来会有一个结果。

> 如果您曾经在旧版 JavaScript 代码中处理过“回调地狱”，那么您很幸运。由于`await`关键字的魔力，处理.NET 中的异步代码要容易得多！`await`让您的代码在异步操作上暂停，然后在底层数据库或网络请求完成时继续执行。与此同时，您的应用程序不会被阻塞，因为它可以根据需要处理其他请求。这种模式很简单，但需要一点时间来适应，所以如果一开始不明白也不要担心。只需继续跟着做！

唯一的注意事项是，您需要更新`Index`方法的签名，使其返回`Task<IActionResult>`而不仅仅是`IActionResult`，并将其标记为`async`：

```
public async Task<IActionResult> Index() {
    var todoItems = await _todoItemService.GetIncompleteItemsAsync();

    // Put items into a model

    // Pass the view to a model and render
} 
```

您已经接近成功了！您让`TodoController`依赖于`ITodoItemService`接口，但还没有告诉 ASP.NET Core 您希望`FakeTodoItemService`是实际在幕后使用的服务。现在可能显而易见，因为您只有一个实现`ITodoItemService`的类，但以后您将有多个实现相同接口的类，因此明确是必要的。

声明（或“连接”）每个接口要使用的具体类是在`Startup`类的`ConfigureServices`方法中完成的。目前，它看起来像这样：

**Startup.cs**

```
public void ConfigureServices(IServiceCollection services) {
    // (... some code)

    services.AddMvc();
} 
```

`ConfigureServices` 方法的作用是向**服务容器**添加东西，或者说是 ASP.NET Core 知道的服务集合。`services.AddMvc` 行添加了内部 ASP.NET Core 系统需要的服务（试验一下，尝试注释掉这行）。任何你想在应用程序中使用的其他服务都必须在这里的 `ConfigureServices` 中添加到服务容器中。

在 `ConfigureServices` 方法的任何地方添加以下行：

```
services.AddSingleton<ITodoItemService, FakeTodoItemService>(); 
```

这行代码告诉 ASP.NET Core，在构造函数（或其他任何地方）请求`ITodoItemService`接口时，使用`FakeTodoItemService`。

`AddSingleton` 将你的服务添加到服务容器中作为一个**单例**。这意味着只创建一个`FakeTodoItemService`的副本，并且在请求服务时重复使用它。稍后，当你编写一个与数据库交互的不同服务类时，你将使用不同的方法（称为**scoped**）。我会在*使用数据库*章节中解释原因。

就是这样！当请求到达并被路由到 `TodoController` 时，ASP.NET Core 将查看可用的服务，并在控制器请求`ITodoItemService`时自动提供`FakeTodoItemService`。因为控制器依赖的服务是从服务容器中“注入”的，所以这种模式被称为**依赖注入**。

# 完成控制器

## 完成控制器

最后一步是完成控制器代码。控制器现在有了来自服务层的待办事项列表，它需要将这些项目放入一个`TodoViewModel`中，并将该模型绑定到你之前创建的视图中：

**`Controllers/TodoController.cs`**

```
public async Task<IActionResult> Index() {
    var todoItems = await _todoItemService.GetIncompleteItemsAsync();

    var model = new TodoViewModel()
    {
        Items = todoItems
    };

    return View(model);
} 
```

如果你还没有，请确保这些`using`语句在文件的顶部：

```
using AspNetCoreTodo.Services;
using AspNetCoreTodo.Models; 
```

如果你在使用 Visual Studio 或者 Visual Studio Code，当你将光标放在红色波浪线上时，编辑器会建议这些`using`语句。

## 测试一下

要启动应用程序，请按 F5（如果你使用的是 Visual Studio 或 Visual Studio Code），或者在终端中运行 `dotnet run`。如果代码编译没有错误，服务器将默认在端口 5000 上启动。

如果你的网络浏览器没有自动打开，请打开它并导航到 [`localhost:5000/todo`](http://localhost:5000/todo)。你将看到你从假数据库层拉取的数据填充了你之前创建的视图。

恭喜！你已经构建了一个可工作的 ASP.NET Core 应用程序。接下来，你将通过第三方包和真实的数据库代码进一步完善它。
