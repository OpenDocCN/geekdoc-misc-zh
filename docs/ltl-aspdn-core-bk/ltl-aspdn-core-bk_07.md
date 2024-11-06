# 自动化测试

# 自动化测试

编写测试是构建任何应用程序的重要部分。测试代码可以帮助您发现和避免错误，并使以后重构代码时更容易，而不会破坏功能或引入新问题。

在本章中，您将学习如何编写既包括**单元测试**又包括**集成测试**的 ASP.NET Core 应用程序。单元测试是小型测试，用于确保单个方法或几行代码正常工作。集成测试（有时称为**功能**测试）是更大的测试，模拟真实场景并测试应用程序的多个层或部分。

# 单元测试

## 单元测试

单元测试是小型、快速的测试，用于检查单个方法或逻辑块的行为。与测试整个类组或整个系统（如集成测试所做的）不同，单元测试依赖于**模拟**或替换方法所依赖的对象。

例如，`TodoController`有两个依赖项：`ITodoItemService`和`UserManager`。而`TodoItemService`又依赖于`ApplicationDbContext`。（你可以从`TodoController` -> `TodoItemService` -> `ApplicationDbContext`画一条线的概念被称为*依赖图*）。

当应用程序正常运行时，ASP.NET Core 依赖注入系统会在创建`TodoController`或`TodoItemService`时将这些对象注入到依赖图中。

另一方面，当您编写单元测试时，您将手动注入模拟或仅供测试使用的这些依赖项。这意味着您可以仅隔离您正在测试的类或方法中的逻辑。（如果您正在测试一个服务，您不希望意外地写入数据库！）

### 创建一个测试项目

为了保持项目的整洁和有序，将测试单独创建一个项目是一种常见做法。新的测试项目应该位于与主项目目录相邻（而非内部）的目录中。

如果您当前在项目目录中，向上`cd`一级。（此目录也将被称为`AspNetCoreTodo`）。然后使用以下命令创建一个新的测试项目：

```
mkdir AspNetCoreTodo.UnitTests
cd AspNetCoreTodo.UnitTests
dotnet new xunit 
```

xUnit.NET 是用于 .NET 代码的流行测试框架，可用于编写单元测试和集成测试。与其他一切一样，它是一组可以安装在任何项目中的 NuGet 包。`dotnet new xunit`模板已经包含了您所需的一切。

现在，您的目录结构应该如下所示：

```
AspNetCoreTodo/
    AspNetCoreTodo/
        AspNetCoreTodo.csproj
        Controllers/
        (etc...)

    AspNetCoreTodo.UnitTests/
        AspNetCoreTodo.UnitTests.csproj 
```

由于测试项目将使用主项目中定义的类，因此您需要向主项目添加引用：

```
dotnet add reference ../AspNetCoreTodo/AspNetCoreTodo.csproj 
```

删除自动创建的`UnitTest1.cs`文件。您已准备好编写第一个测试了。

### 编写一个服务测试

查看`TodoItemService`的`AddItemAsync`方法中的逻辑：

```
public async Task<bool> AddItemAsync(NewTodoItem newItem, ApplicationUser user) {
    var entity = new TodoItem
    {
        Id = Guid.NewGuid(),
        OwnerId = user.Id,
        IsDone = false,
        Title = newItem.Title,
        DueAt = DateTimeOffset.Now.AddDays(3)
    };

    _context.Items.Add(entity);

    var saveResult = await _context.SaveChangesAsync();
    return saveResult == 1;
} 
```

在将新项目保存到数据库之前，此方法会对新项目做出一些决定或假设：

+   `OwnerId`属性应设置为用户的 ID

+   新项目应始终为未完成状态（`IsDone = false`）

+   新项目的标题应从`newItem.Title`复制

+   新项目应始终在 3 天后到期

> 你的代码所做出的这些决定被称为*业务逻辑*，因为它与你的应用程序的目的或"业务"有关的逻辑。业务逻辑的其他示例包括根据产品价格和税率计算总费用，或检查玩家是否有足够的点数在游戏中升级。

这些决定是有意义的，而且也有必要编写一个测试以确保这个逻辑在未来不会改变。（想象一下，如果你或其他人重构了`AddItemAsync`方法，并且忘记了其中一个假设。当你的服务很简单时可能不太可能，但是当你的应用程序变得更加复杂时，拥有自动化检查变得非常重要。）

要编写一个单元测试来验证`TodoItemService`中的逻辑，可以在测试项目中创建一个新类：

**`AspNetCoreTodo.UnitTests/TodoItemServiceShould.cs`**

```
using System;
using System.Threading.Tasks;
using AspNetCoreTodo.Data;
using AspNetCoreTodo.Models;
using AspNetCoreTodo.Services;
using Microsoft.EntityFrameworkCore;
using Xunit;

namespace AspNetCoreTodo.UnitTests
{
    public class TodoItemServiceShould
    {
        [Fact]
        public async Task AddNewItem() {
            // ...
        }
    }
} 
```

`[Fact]`属性来自 xUnit.NET 包，它标记了这个方法作为一个测试方法。

> 有许多不同的测试命名和组织方式，各有利弊。我喜欢在我的测试类中加上`Should`后缀，以创建一个可读的句子与测试方法名，但请随意使用你自己的风格！

`TodoItemService`需要一个`ApplicationDbContext`，通常连接到你的开发或生产数据库。你不希望在测试中使用它。相反，你可以在测试代码中使用 Entity Framework Core 的内存数据库提供程序。由于整个数据库存在于内存中，每次重新启动测试时都会被清除。而且，由于它是一个合适的 Entity Framework Core 提供程序，`TodoItemService`不会知道区别！

使用`DbContextOptionsBuilder`配置内存数据库提供程序，然后调用`AddItem`：

```
var options = new DbContextOptionsBuilder<ApplicationDbContext>()
    .UseInMemoryDatabase(databaseName: "Test_AddNewItem").Options;

// Set up a context (connection to the DB) for writing
using (var inMemoryContext = new ApplicationDbContext(options))
{
    var service = new TodoItemService(inMemoryContext);

    var fakeUser = new ApplicationUser
    {
        Id = "fake-000",
        UserName = "fake@fake"
    };

    await service.AddItemAsync(new NewTodoItem { Title = "Testing?" }, fakeUser);
} 
```

最后一行创建了一个名为`Testing?`的新待办事项，并告诉服务将其保存到（内存中的）数据库。为了验证业务逻辑是否正确运行，检索该项：

```
// Use a separate context to read the data back from the DB
using (var inMemoryContext = new ApplicationDbContext(options))
{
    Assert.Equal(1, await inMemoryContext.Items.CountAsync());

    var item = await inMemoryContext.Items.FirstAsync();
    Assert.Equal("Testing?", item.Title);
    Assert.Equal(false, item.IsDone);
    Assert.True(DateTimeOffset.Now.AddDays(3) - item.DueAt < TimeSpan.FromSeconds(1));
} 
```

第一个验证步骤是一个健全性检查：不应该有多个项目保存到内存数据库中。假设这是真的，测试使用`FirstAsync`检索保存的项目，然后断言属性设置为预期值。

断言 datetime 值有点棘手，因为即使毫秒组件不同，比较两个日期是否相等也会失败。相反，测试检查`DueAt`值是否与预期值相差不到一秒。

> 单元测试和集成测试通常遵循 AAA（安排-执行-断言）模式：首先设置对象和数据，然后执行某些操作，最后测试检查（断言）预期的行为是否发生。

这是`AddNewItem`测试的最终版本：

**`AspNetCoreTodo.UnitTests/TodoItemServiceShould.cs`**

```
public class TodoItemServiceShould
{
    [Fact]
    public async Task AddNewItem() {
        var options = new DbContextOptionsBuilder<ApplicationDbContext>()
            .UseInMemoryDatabase(databaseName: "Test_AddNewItem")
            .Options;

        // Set up a context (connection to the DB) for writing
        using (var inMemoryContext = new ApplicationDbContext(options))
        {
            var service = new TodoItemService(inMemoryContext);
            await service.AddItemAsync(new NewTodoItem { Title = "Testing?" }, null);
        }

        // Use a separate context to read the data back from the DB
        using (var inMemoryContext = new ApplicationDbContext(options))
        {
            Assert.Equal(1, await inMemoryContext.Items.CountAsync());

            var item = await inMemoryContext.Items.FirstAsync();
            Assert.Equal("Testing?", item.Title);
            Assert.Equal(false, item.IsDone);
            Assert.True(DateTimeOffset.Now.AddDays(3) - item.DueAt < TimeSpan.FromSeconds(1));
        }
    }
} 
```

### 运行测试

在终端上，运行这个命令（确保你仍在`AspNetCoreTodo.UnitTests`目录中）：

```
dotnet test 
```

`test`命令会扫描当前项目中的测试（在这种情况下标记为`[Fact]`属性），并运行找到的所有测试。你会看到类似于以下输出：

```
Starting test execution, please wait...
[xUnit.net 00:00:00.7595476]   Discovering: AspNetCoreTodo.UnitTests
[xUnit.net 00:00:00.8511683]   Discovered:  AspNetCoreTodo.UnitTests
[xUnit.net 00:00:00.9222450]   Starting:    AspNetCoreTodo.UnitTests
[xUnit.net 00:00:01.3862430]   Finished:    AspNetCoreTodo.UnitTests

Total tests: 1\. Passed: 1\. Failed: 0\. Skipped: 0.
Test Run Successful.
Test execution time: 1.9074 Seconds 
```

现在你有一个测试覆盖`TodoItemService`。作为额外挑战，尝试编写确保的单元测试：

+   如果传递一个不存在的 ID，`MarkDoneAsync`会返回 false

+   当使一个有效项目完成时，`MarkDoneAsync`会返回 true

+   `GetIncompleteItemsAsync`仅返回特定用户拥有的项目

# 集成测试

## 集成测试

与单元测试相比，集成测试涵盖整个应用程序堆栈（路由、控制器、服务、数据库）。集成测试不是隔离一个类或组件，而是确保应用程序的所有组件正常协同工作。

集成测试比单元测试更慢、更复杂，因此一个项目通常会有很多单元测试，但只有少数几个集成测试。

为了测试整个堆栈（包括控制器路由），集成测试通常会像网页浏览器一样向应用程序发出 HTTP 调用。

要编写进行 HTTP 请求的集成测试，你可以手动启动应用程序运行请求到`http://localhost:5000`的测试（希望应用程序仍在运行）。然而，ASP.NET Core 提供了一个更好的方法来为测试托管你的应用程序：使用`TestServer`类。`TestServer`可以在测试期间托管你的应用程序，然后在测试完成时自动停止它。

### 创建一个测试项目

你可以将单元测试和集成测试放在同一个项目中（随意这样做），但为了完整起见，我将向你展示如何为集成测试创建一个单独的项目。

如果你当前在项目目录中，`cd`到基本的`AspNetCoreTodo`目录。使用以下命令创建一个新的测试项目：

```
mkdir AspNetCoreTodo.IntegrationTests
cd AspNetCoreTodo.IntegrationTests
dotnet new xunit 
```

现在你的目录结构应该是这样的：

```
AspNetCoreTodo/
    AspNetCoreTodo/
        AspNetCoreTodo.csproj
        Controllers/
        (etc...)

    AspNetCoreTodo.UnitTests/
        AspNetCoreTodo.UnitTests.csproj

    AspNetCoreTodo.IntegrationTests/
        AspNetCoreTodo.IntegrationTests.csproj 
```

由于测试项目将使用主项目中定义的类，所以你需要向主项目添加一个引用：

```
dotnet add reference ../AspNetCoreTodo/AspNetCoreTodo.csproj 
```

你还需要添加`Microsoft.AspNetCore.TestHost` NuGet 包：

```
dotnet add package Microsoft.AspNetCore.TestHost 
```

删除由`dotnet new`创建的`UnitTest1.cs`文件。你已经准备好编写集成测试了。

### 编写一个集成测试

在每个测试之前，测试服务器需要配置一些东西。你可以将这些设置代码提取到一个单独的类中，而不是在测试中混杂这些设置代码。创建一个名为`TestFixture`的新类：

**`AspNetCoreTodo.IntegrationTests/TestFixture.cs`**

```
using System;
using System.Collections.Generic;
using System.IO;
using System.Net.Http;
using Microsoft.AspNetCore.Hosting;
using Microsoft.AspNetCore.TestHost;
using Microsoft.Extensions.Configuration;

namespace AspNetCoreTodo.IntegrationTests
{
    public class TestFixture : IDisposable  
    {
        private readonly TestServer _server;

        public TestFixture() {
            var builder = new WebHostBuilder()
                .UseStartup<AspNetCoreTodo.Startup>()
                .ConfigureAppConfiguration((context, configBuilder) =>
                {
                    configBuilder.SetBasePath(Path.Combine(
                        Directory.GetCurrentDirectory(), "..\\..\\..\\..\\AspNetCoreTodo"));

                    configBuilder.AddJsonFile("appsettings.json");

                    // Add fake configuration for Facebook middleware (to avoid startup errors)
                    configBuilder.AddInMemoryCollection(new Dictionary<string, string>()
                    {
                        ["Facebook:AppId"] = "fake-app-id",
                        ["Facebook:AppSecret"] = "fake-app-secret"
                    });
                });
            _server = new TestServer(builder);

            Client = _server.CreateClient();
            Client.BaseAddress = new Uri("http://localhost:5000");
        }

        public HttpClient Client { get; }

        public void Dispose() {
            Client.Dispose();
            _server.Dispose();
        }
    }
} 
```

这个类负责设置一个`TestServer`，并有助于保持测试本身的整洁。

> 如果你在*安全和身份*章节中配置了 Facebook 登录，那么有必要为 Facebook 应用程序的 ID 和密钥添加假值（在上面的`ConfigureAppConfiguration`块中）。这是因为测试服务器无法访问 Secrets Manager 中的值。在这个 Fixture 类中添加一些假值将防止测试服务器启动时出错。

现在你（真的）准备好写一个集成测试了。创建一个名为`TodoRouteShould`的新类：

**`AspNetCoreTodo.IntegrationTests/TodoRouteShould.cs`**

```
using System.Net;
using System.Net.Http;
using System.Threading.Tasks;
using Xunit;

namespace AspNetCoreTodo.IntegrationTests
{
    public class TodoRouteShould : IClassFixture<TestFixture>
    {
        private readonly HttpClient _client;

        public TodoRouteShould(TestFixture fixture)
        {
            _client = fixture.Client;
        }

        [Fact]
        public async Task ChallengeAnonymousUser()
        {
            // Arrange
            var request = new HttpRequestMessage(HttpMethod.Get, "/todo");

            // Act: request the /todo route
            var response = await _client.SendAsync(request);

            // Assert: anonymous user is redirected to the login page
            Assert.Equal(HttpStatusCode.Redirect, response.StatusCode);
            Assert.Equal("http://localhost:5000/Account/Login?ReturnUrl=%2Ftodo",
                        response.Headers.Location.ToString());
        }
    }
} 
```

这个测试发出一个匿名（未登录）请求到`/todo`路由，并验证浏览器是否被重定向到登录页面。

这种情景非常适合作为一个集成测试的候选项，因为它涉及到应用程序的多个组件：路由系统、控制器、控制器标记为`[Authorize]`等等。这也是一个很好的测试，因为它确保你永远不会意外地移除`[Authorize]`属性，使得待办事项视图对所有人都可访问。

在终端中使用`dotnet test`运行测试。如果一切正常，你将会看到一个成功的消息：

```
Starting test execution, please wait...
[xUnit.net 00:00:00.7237031]   Discovering: AspNetCoreTodo.IntegrationTests
[xUnit.net 00:00:00.8118035]   Discovered:  AspNetCoreTodo.IntegrationTests
[xUnit.net 00:00:00.8779059]   Starting:    AspNetCoreTodo.IntegrationTests
[xUnit.net 00:00:01.5828576]   Finished:    AspNetCoreTodo.IntegrationTests

Total tests: 1\. Passed: 1\. Failed: 0\. Skipped: 0.
Test Run Successful.
Test execution time: 2.0588 Seconds 
```

## 总结

测试是一个广泛的话题，还有很多东西可以学习。本章没有涉及 UI 测试或测试前端（JavaScript）代码，这可能值得单独写一整本书。不过，你应该具备练习和学习为自己的应用程序编写测试的技能和基础知识。

和往常一样，ASP.NET Core 文档([`docs.asp.net`](https://docs.asp.net))和 StackOverflow 都是学习更多知识和在遇到困难时寻找答案的好资源。
