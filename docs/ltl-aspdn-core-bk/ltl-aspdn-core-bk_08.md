# 部署应用程序

# 部署应用程序

您已经走了很长一段路，但还没有完成。一旦创建了一个很棒的应用程序，您需要与世界分享！

因为 ASP.NET Core 应用程序可以在 Windows、Mac 或 Linux 上运行，所以有许多不同的方式可以部署您的应用程序。在本章中，我将向您展示最常见（也是最简单）的上线方式。

## 部署选项

ASP.NET Core 应用程序通常部署到以下环境之一：

+   **任何 Docker 主机**。任何能够托管 Docker 容器的机器都可以用来托管 ASP.NET Core 应用程序。创建 Docker 镜像是快速部署应用程序的一种方法，特别是如果您熟悉 Docker 的话。（如果不熟悉，不用担心！我稍后会介绍步骤。）

+   **Azure**。Microsoft Azure 原生支持 ASP.NET Core 应用程序。如果您有 Azure 订阅，只需创建一个 Web 应用程序并上传您的项目��件即可。我将在下一节中介绍如何使用 Azure CLI 执行此操作。

+   **Linux（使用 Nginx）**。如果您不想使用 Docker，仍然可以在任何 Linux 服务器上托管您的应用程序（包括 Amazon EC2 和 DigitalOcean 虚拟机）。将 ASP.NET Core 与 Nginx 反向代理配对是很典型的做法。（下面会更多介绍 Nginx。）

+   **Windows**。您可以在 Windows 上使用 IIS Web 服务器来托管 ASP.NET Core 应用程序。通常更容易（和更便宜）只需部署到 Azure，但如果您更喜欢自己管理 Windows 服务器，也可以正常工作。

## Kestrel 和反向代理

> 如果您不关心托管 ASP.NET Core 应用程序的内部机制，只想要逐步说明，请随时跳到接下来的两个部分之一！

ASP.NET Core 包含一个快速、轻量级的开发 Web 服务器，称为 Kestrel。每次在本地运行应用程序并浏览`http://localhost:5000`时，您都在使用该服务器。当将应用程序部署到生产环境时，它仍将在后台使用 Kestrel。但建议您在 Kestrel 前面放置一个反向代理，因为 Kestrel 尚未具有负载平衡和其他更大型 Web 服务器具有的功能。

在 Linux（和 Docker 容器）上，您可以使用 Nginx 或 Apache Web 服务器接收来自互联网的请求，并将它们路由到使用 Kestrel 托管的应用程序。如果您在 Windows 上，IIS 也会执行相同的操作。

如果您正在使用 Azure 托管您的应用程序，这一切都会自动为您处理。我将在 Docker 部分中介绍设置 Nginx 作为反向代理的内容。

# 部署到 Azure

## 部署到 Azure

将 ASP.NET Core 应用程序部署到 Azure 只需几个步骤。您可以通过 Azure Web 门户进行操作，或者使用 Azure CLI 命令行。我将介绍后者。

### 您需要什么

+   Git（使用`git --version`确保已安装）

+   Azure CLI（按照[`github.com/Azure/azure-cli`](https://github.com/Azure/azure-cli)的安装说明进行安装）

+   一个 Azure 订阅（免费订阅可以）

+   在你的项目根目录中创建一个部署配置文件

### 创建一个部署配置文件

由于你的目录结构中有多个项目（Web 应用程序和两个测试项目），Azure 不知道应该向世界展示哪一个。为了解决这个问题，在你的目录结构的顶部创建一个名为`.deployment`的文件：

**`.deployment`**

```
[config]
project = AspNetCoreTodo/AspNetCoreTodo.csproj 
```

确保将文件保存为`.deployment`，不要有其他部分的名称。（在 Windows 上，你可能需要在文件名周围加上引号，如`".deployment"`，以防止添加`.txt`扩展名。）

如果在你的顶级目录中执行`ls`或`dir`命令，你应该看到这些项目：

```
.deployment
AspNetCoreTodo
AspNetCoreTodo.IntegrationTests
AspNetCoreTodo.UnitTests 
```

### 设置 Azure 资源

如果你是第一次安装 Azure CLI，请运行

```
az login 
```

并按照提示在你的计算机上登录。然后，为该应用程序创建一个新的资源组：

```
az group create -l westus -n AspNetCoreTodoGroup 
```

这将在西部美国地区创建一个资源组。如果你距离西部美国很远，请使用`az account list-locations`获取位置列表，并找到一个更靠近你的地方。

接下来，在刚创建的组中创建一个应用服务计划：

```
az appservice plan create -g AspNetCoreTodoGroup -n AspNetCoreTodoPlan --sku F1 
```

> 侧边栏：`F1`是免费应用计划。如果你想要在应用程序中使用自定义域名，请使用 D1（每月$10）计划或更高级别的计划。

现在在应用服务计划中创建一个 Web 应用程序：

```
az webapp create -g AspNetCoreTodoGroup -p AspNetCoreTodoPlan -n MyTodoApp 
```

应用程序的名称（上面为`MyTodoApp`）在 Azure 中必须是全局唯一的。一旦应用程序创建完成，它将有一个默认的 URL 格式：[`mytodoapp.azurewebsites.net`](http://mytodoapp.azurewebsites.net)

### 更新应用程序设置

> 侧边栏：只有在*安全性和身份*章节中配置了 Facebook 登录时才需要这样做。

如果缺少`Facebook:AppId`和`Facebook:AppSecret`配置值，你的应用程序将无法正确启动。你需要使用 Azure Web 门户添加这些值：

1.  通过[`portal.azure.com`](https://portal.azure.com)登录到你的 Azure 账户

1.  打开你的 Web 应用程序（上面称为`MyTodoApp`）

1.  点击**应用程序设置**选项卡

1.  在**应用设置**部分中，添加`Facebook:AppId`和`Facebook:AppSecret`及其相应的值

1.  点击顶部的**保存**

### 将项目文件部署到 Azure

你可以使用 Git 将应用程序文件推送到 Azure Web 应用程序。如果你的本地目录还没有被跟踪为 Git 仓库，请运行以下命令进行设置：

```
git init
git add .
git commit -m "First commit!" 
```

接下来，为部署创建一个 Azure 用户名和密码：

```
az webapp deployment user set --user-name nate 
```

按照说明创建一个密码。然后使用`config-local-git`输出一个 Git URL：

```
az webapp deployment source config-local-git -g AspNetCoreTodoGroup -n MyTodoApp --out tsv

https://nate@mytodoapp.scm.azurewebsites.net/MyTodoApp.git 
```

将 URL 复制到剪贴板，并使用它添加一个 Git 远程到你的本地仓库：

```
git remote add azure <paste> 
```

你只需要执行这些步骤一次。现在，每当你想要将应用程序文件推送到 Azure 时，请使用 Git 进行检入并运行

```
git push azure master 
```

应用程序部署到 Azure 时，您将看到一系列日志消息。完成后，请浏览 [`yourappname.azurewebsites.net`](http://yourappname.azurewebsites.net) 查看！

# 使用 Docker 部署

## 使用 Docker 部署

像 Docker 这样的容器化技术可以大大简化部署 Web 应用程序的过程。您不再需要花时间配置服务器以满足运行应用程序所需的依赖关系，复制文件并重新启动进程，您只需创建一个包含应用程序运行所需一切的 Docker 镜像，并在任何 Docker 主机上将其作为容器启动。

Docker 还可以使跨多个服务器扩展应用程序变得更加容易。一旦有了镜像，使用它创建 1 ��容器的过程与创建 100 个容器的过程相同。

在开始之前，您需要在开发机器上安装 Docker CLI。搜索 "get docker for (mac/windows/linux)" 并按照官方 Docker 网站上的说明进行操作。您可以通过以下方式验证是否正确安装：

```
docker --version 
```

> 如果在 *安全性和身份* 章节中设置了 Facebook 登录，则需要使用 Docker secrets 在容器内部安全设置 Facebook 应用程序密钥。处理 Docker secrets 超出了本书的范围。如果愿意，您可以在 `ConfigureServices` 方法中注释掉 `AddFacebook` 行以禁用 Facebook 登录。

### 添加一个 Dockerfile

您需要的第一件事是一个 Dockerfile，它类似于告诉 Docker 您的应用程序需要什么的配方。

在 Web 应用程序根目录中创建一个名为 `Dockerfile`（无扩展名）的文件，与 `Program.cs` 并排。在您喜欢的编辑器中打开它。写入以下行：

```
FROM microsoft/dotnet:latest 
```

这告诉 Docker 从微软发布的现有镜像启动您的镜像。这将确保容器具有运行 ASP.NET Core 应用程序所需的一切。

```
COPY . /app 
```

`COPY` 命令将您本地目录的内容（应用程序的源代码）复制到 Docker 镜像中名为 `/app` 的目录中。

```
WORKDIR /app 
```

`WORKDIR` 是 `cd` 的 Docker 等效命令。Dockerfile 中的其余命令将从 `/app` 文件夹内运行。

```
RUN ["dotnet", "restore"] RUN ["dotnet", "build"] 
```

这些命令将执行 `dotnet restore`（下载应用程序所需的 NuGet 包）和 `dotnet build`（编译应用程序）。

```
EXPOSE 5000/tcp 
```

默认情况下，Docker 容器不会向外部世界公开任何网络端口。您必须明确告诉 Docker 您的应用程序将在端口 5000 上通信（默认的 Kestrel 端口）。

```
ENV ASPNETCORE_URLS http://*:5000 
```

`ENV` 命令在容器中设置环境变量。`ASPNETCORE_URLS` 变量告诉 ASP.NET Core 应绑定到哪个网络接口和端口。

```
ENTRYPOINT ["dotnet", "run"] 
```

Dockerfile 的最后一行使用 `dotnet run` 命令启动您的应用程序。Kestrel 将开始监听端口 5000，就像在本地机器上使用 `dotnet run` 时一样。

完整的 Dockerfile 如下所示：

**`Dockerfile`**

```
FROM microsoft/dotnet:latest
COPY . /app WORKDIR /app RUN ["dotnet", "restore"] RUN ["dotnet", "build"] EXPOSE 5000/tcp
ENV ASPNETCORE_URLS http://*:5000
ENTRYPOINT ["dotnet", "run"] 
```

### 创建一个镜像

确保 Dockerfile 已保存，然后使用 `docker build` 创建一个镜像：

```
docker build -t aspnetcoretodo . 
```

不要忘记末尾的句点！这告诉 Docker 在当前目录中查找 Dockerfile。

创建完镜像后，您可以运行`docker images`来列出本地机器上所有可用的镜像。要在容器中测试它，运行

```
docker run -it -p 5000:5000 aspnetcoretodo 
```

`-it` 标志告诉 Docker 以交互模式运行容器。当您想要停止容器时，按下`Control-C`。

### 设置 Nginx

在本章的开头，我提到您应该使用像 Nginx 这样的反向代理来代理请求到 Kestrel。您也可以使用 Docker 来实现这一点。

整体架构将包括两个容器：一个监听端口 80 的 Nginx 容器，将请求转发到运行 Kestrel 并监听端口 5000 的独立容器。

Nginx 容器需要自己的 Dockerfile。为了避免与刚刚创建的 Dockerfile 冲突，创建一个新目录在 Web 应用程序根目录中：

```
mkdir nginx 
```

创建一个新的 Dockerfile 并添加以下内容：

**`nginx/Dockerfile`**

```
FROM nginx
COPY nginx.conf /etc/nginx/nginx.conf 
```

接下来，创建一个`nginx.conf`文件：

**`nginx/nginx.conf`**

```
events { worker_connections 1024; }

http {

        server {
              listen 80;

              location / {
                proxy_pass http://kestrel:5000;
                proxy_http_version 1.1;
                proxy_set_header Upgrade $http_upgrade;
                proxy_set_header Connection 'keep-alive';
                proxy_set_header Host $host;
                proxy_cache_bypass $http_upgrade;
              }
        }
} 
```

这个配置文件告诉 Nginx 将传入的请求代理到`http://kestrel:5000`。（您很快就会明白为什么`kestrel:5000`有效。）

### 设置 Docker Compose

还有一个文件需要创建。在 Web 应用程序根目录中，创建`docker-compose.yml`：

**`docker-compose.yml`**

```
nginx:
 build: ./nginx
 links:
 - kestrel:kestrel
 ports:
 - "80:80"
kestrel:
 build: .
 ports:
 - "5000" 
```

Docker Compose 是一个帮助您创建和运行多容器应用程序的工具。这个配置文件定义了两个容器：从`./nginx/Dockerfile`配方创建的`nginx`，以及从`./Dockerfile`配方创建的`kestrel`。这些容器被明确地链接在一起，以便它们可以通信。

您可以尝试通过运行以下命令来启动整个多容器应用程序：

```
docker-compose up 
```

尝试打开浏览器并导航到`http://localhost`（不是 5000！）。Nginx 在端口 80（默认 HTTP 端口）上监听，并将请求代理到由 Kestrel 托管的 ASP.NET Core 应用程序。

### 设置 Docker 服务器

具体的设置说明超出了这本小书的范围，但任何现代 Linux 发行版（如 Ubuntu）都可以设置为 Docker 主机。例如，您可以在 Amazon EC2 上创建一个虚拟机，并安装 Docker 服务。您可以搜索"amazon ec2 set up docker"（例如）以获取说明。

我更喜欢 DigitalOcean，因为他们让入门变得非常容易。DigitalOcean 既有预构建的 Docker 虚拟机，也有深入的教程来帮助您启动 Docker（搜索"digitalocean docker"）。
