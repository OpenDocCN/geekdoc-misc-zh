# 使用 libcurl 的 HTTP

# 使用 libcurl 的 HTTP

HTTP 是 libcurl 用户最常用的协议，libcurl 提供了无数种修改这种传输的方式。请参阅 HTTP 协议基础知识了解 HTTP 协议的基础知识。

## HTTPS

待定

## HTTP 代理

待定

# HTTP 响应

# HTTP 响应

每个 HTTP 请求都包含一个 HTTP 响应。HTTP 响应是一组元数据和一个响应主体，其中主体有时可能为零字节，因此不存在。但是 HTTP 响应始终会有响应头。

响应主体将传递给写回调，响应头将传递给头回调，但有时应用程序只想知道数据的大小。

可以通过以下方式使用`curl_easy_getinfo()`提取服务器头告知的响应大小：

```
double size;
curl_easy_getinfo(curl, CURLINFO_CONTENT_LENGTH_DOWNLOAD, &size); 
```

但是，如果您可以等到传输完成后再执行此操作，这也是一种更可靠的方法，因为并非所有 URL 都会提供立即大小（例如对于按需生成内容的服务器）。您可以询问最近传输的下载数据量。

```
double size;
curl_easy_getinfo(curl, CURLINFO_SIZE_DOWNLOAD, &size); 
```

## HTTP 响应代码

每个 HTTP 响应都以包含 HTTP 响应代码的单行开头。它是一个三位数，包含服务器对请求的状态的想法。这些数字在 HTTP 标准规范中有详细说明，但它们被分成基本上如下工作的范围：

| 代码 | 含义 |
| --- | --- |
| 1xx | 临时代码，后面跟着一个新的 |
| 2xx | 一切正常 |
| 3xx | 内容在其他地方 |
| 4xx | 由于客户端问题而失败 |
| 5xx | 由于服务器问题失败 |

您可以像这样在传输后提取响应代码

```
long code;
curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code); 
```

## 关于 HTTP 响应代码“错误”

虽然响应代码数字可能包括服务器用于表示处理请求时出现错误的数字（在 4xx 和 5xx 范围内），但重要的是要意识到这不会导致 libcurl 返回错误。

当要求 libcurl 执行 HTTP 传输时，如果该 HTTP 传输失败，它将返回错误。但是，得到 HTTP 404 或类似错误对于 libcurl 来说不是问题。这不是 HTTP 传输错误。用户很可能正在编写一个用于测试服务器 HTTP 响应的客户端。

如果您坚持要求 curl 将 400 及以上的 HTTP 响应代码视为错误，libcurl 提供了`CURLOPT_FAILONERROR`选项，如果设置了该选项，curl 会在这种情况下返回`CURLE_HTTP_RETURNED_ERROR`。然后它会尽快返回错误，而不会传递响应主体。

# HTTP 请求

# HTTP 请求

当 curl 发送告诉服务器要做什么时，curl 发送的是 HTTP 请求。当它想要获取数据或发送数据时。所有涉及 HTTP 的传输都始于 HTTP 请求。

HTTP 请求包含方法、路径、HTTP 版本和一组请求头。当然，使用 libcurl 的应用程序可以调整所有这些字段。

## 请求方法

每个 HTTP 请求都包含一个"方法"，有时也称为"动词"。它通常是像 GET、HEAD、POST 或 PUT 这样的东西，但也有更奇特的，像 DELETE、PATCH 和 OPTIONS。

通常当你使用 libcurl 来设置和执行传输时，特定的请求方法会由你使用的选项隐含。如果你只要求一个 URL，这意味着方法将是 `GET`，而如果你设置例如 `CURLOPT_POSTFIELDS`，那么 libcurl 将使用 `POST` 方法。如果你将 `CURLOPT_UPLOAD` 设置为 true，libcurl 将在其 HTTP 请求中发送一个 `PUT` 方法，依此类推。要求 `CURLOPT_NOBODY` 将使 libcurl 使用 `HEAD`。

然而，有时这些默认的 HTTP 方法不够好或者根本不是你希望你的传输使用的方法。那么你可以使用 `CURLOPT_CUSTOMREQUEST` 指示 libcurl 使用你喜欢的特定方法。例如，你想要向你选择的 URL 发送一个 `DELETE` 方法：

```
curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, "DELETE");
curl_easy_setopt(curl, CURLOPT_URL, "https://example.com/file.txt"); 
```

CURLOPT_CUSTOMREQUEST 设置应该仅是用作 HTTP 请求行中方法的单个关键字。如果你想要更改或添加额外的 HTTP 请求头部，请参阅以下部分。

## 自定义 HTTP 请求头部

当 libcurl 发出 HTTP 请求作为执行你要求它执行的数据传输的一部分时，它当然会带着一组适合完成任务的 HTTP 头部发送它们。

如果只给出 URL "[`localhost/file1.txt`](http://localhost/file1.txt)"，libcurl 7.51.0 将向服务器发送以下请求：

```
GET /file1.txt HTTP/1.1
Host: localhost
Accept: */* 
```

如果你相反地指示你的应用程序也将 `CURLOPT_POSTFIELDS` 设置为字符串 "foobar"（6 个字母，引号仅用于视觉定界），它将发送以下头部：

```
POST /file1.txt HTTP/1.1
Host: localhost
Accept: */*
Content-Length: 6
Content-Type: application/x-www-form-urlencoded 
```

如果你对 libcurl 发送的默认头部集合不满意，应用程序可以在 HTTP 请求中添加、更改或删除头部。

### 添加一个头部

要添加一个否则不会在请求中的头部，请使用 `CURLOPT_HTTPHEADER` 添加。假设你想要一个名为 `Name:` 的头部，其中包含 `Mr. Smith`：

```
struct curl_slist *list = NULL;
list = curl_slist_append(list, "Name: Mr Smith");
curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
curl_easy_perform(curl);
curl_slist_free_all(list); /* free the list again */ 
```

### 更改头部

如果其中一个默认头部不符合你的要求，你可以修改它们。比如，如果你认为默认的 `Host:` 头部是错误的（即使它是从你给 libcurl 的 URL 衍生出来的），你可以告诉 libcurl 你自己的：

```
struct curl_slist *list = NULL;
list = curl_slist_append(list, "Host: Alternative");
curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
curl_easy_perform(curl);
curl_slist_free_all(list); /* free the list again */ 
```

### 移除一个头部

当你认为 libcurl 在请求中使用了一个你认为它不应该使用的头部时，你可以很容易地告诉它将其从请求中移除。比如，如果你想要移除 `Accept:` 头部。只需在冒号的右侧提供头部名称而不提供任何内容：

```
struct curl_slist *list = NULL;
list = curl_slist_append(list, "Accept:");
curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
curl_easy_perform(curl);
curl_slist_free_all(list); /* free the list again */ 
```

### 提供一个没有内容的头部

正如你在上面的部分中可能已经注意到的，如果你试图在冒号的右侧添加一个没有内容的头部，它将被视为删除指令，并且它将完全禁止该头部被发送。如果你*真的*想发送一个右侧没有内容的头部，你需要使用一个特殊的标记。你必须在分号而不是正确的冒号后提供头部。比如`Header;`。所以如果你想在发送的 HTTP 请求中添加一个只有`Moo:`而没有跟随冒号的头部，你可以这样写：

```
struct curl_slist *list = NULL;
list = curl_slist_append(list, "Moo;");
curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
curl_easy_perform(curl);
curl_slist_free_all(list); /* free the list again */ 
```

## 引用者

`Referer:`头部（是的，它拼写错误）是一个标准的 HTTP 头部，它告诉服务器用户代理从哪个 URL 被引导到现在请求的 URL 时的来源。它是一个普通的头部，所以你可以像上面展示的`CURLOPT_HEADER`方法一样自己设置它，或者你可以使用称为`CURLOPT_REFERER`的快捷方式。就像这样： 

```
curl_easy_setopt(curl, CURLOPT_REFERER, "https://example.com/fromhere/");
curl_easy_perform(curl); 
```

### 自动引用者

当 libcurl 被要求使用`CURLOPT_FOLLOWLOCATION`选项自己跟随重定向，并且你仍然希望`Referer:`头设置为正确的前一个 URL，从中进行重定向，你可以让 libcurl 自己设置：

```
curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
curl_easy_setopt(curl, CURLOPT_AUTOREFERER, 1L);
curl_easy_setopt(curl, CURLOPT_URL, "https://example.com/redirected.cgi");
curl_easy_perform(curl); 
```

# HTTP 版本

# HTTP 版本

与任何其他互联网协议一样，HTTP 协议随着时间的推移而不断发展，现在有分布在世界各地和时间的不同版本和不同成功级别的客户端和服务器。所以为了让 libcurl 能够处理你在 libcurl 中传递的 URL，libcurl 提供了方法让你指定请求和传输应该使用哪个 HTTP 版本。libcurl 被设计成首先尝试使用最常见的，最明智的默认值，但有时这是不够的，那么你可能需要告诉 libcurl 要做什么。

自 2016 年中期以来，如果你的 libcurl 具有内置的 HTTP/2 能力，libcurl 默认使用 HTTP/2 来处理 HTTPS 服务器，libcurl 将尝试自动使用 HTTP/2，否则在协商失败时会降级到 1.1。不支持 HTTP/2 的 libcurl 默认在 HTTPS 上使用 1.1。普通 HTTP 请求仍然默认使用 HTTP/1.1。

如果默认行为对你的传输不够好，`CURLOPT_HTTP_VERSION`选项可以帮助你。

| 选项 | 描述 |
| --- | --- |
| CURL_HTTP_VERSION_NONE | 重置为默认行为 |
| CURL_HTTP_VERSION_1_0 | 强制使用传统的 HTTP/1.0 协议版本 |
| CURL_HTTP_VERSION_1_1 | 使用 HTTP/1.1 协议版本进行请求 |
| CURL_HTTP_VERSION_2_0 | 尝试使用 HTTP/2 |
| CURL_HTTP_VERSION_2TLS | 仅在 HTTPS 连接上尝试使用 HTTP/2，否则使用 HTTP/1.1 |
| CURL_HTTP_VERSION_2_PRIOR_KNOWLEDGE | 直接使用 HTTP/2，无需从 1.1“升级”。这要求你知道这个服务器支持它。 |

# HTTP 范围

## HTTP 范围

如果客户端只想要远程资源的前 200 字节，或者也许是中间某处的 300 字节怎么办？HTTP 协议允许客户端仅请求特定的数据范围。客户端通过指定起始偏移量和结束偏移量向服务器请求特定范围。它甚至可以结合起来，通过只列出一堆相邻的片段来请求同一请求中的几个范围。当服务器发送多个独立的片段以回答此类请求时，您将用 mime 边界字符串将它们分开，并且将由用户应用程序相应地处理。curl 不会进一步分离这样的响应。

然而，字节范围只是对服务器的一个请求。它不必遵守请求，在许多情况下，比如当服务器在被请求时自动生成内容时，它会简单地拒绝执行，并且它会以任何方式回应完整的内容。

你可以让 libcurl 使用`CURLOPT_RANGE`请求一个范围。比如，如果你想要从某个地方获取前 200 字节：

```
curl_easy_setopt(curl, CURLOPT_RANGE, "0-199"); 
```

或者从索引 200 开始的文件中的所有内容：

```
curl_easy_setopt(curl, CURLOPT_RANGE, "200-"); 
```

从索引 0 获取 200 字节 *以及* 从索引 1000 获取 200 字节：

```
curl_easy_setopt(curl, CURLOPT_RANGE, "0-199,1000-199"); 
```

# 使用 libcurl 处理 cookie

# 使用 libcurl 处理 cookie

默认情况下，libcurl 使传输尽可能基本，并且需要启用功能才能使用。其中一个功能就是 HTTP cookie，更为人所知的是“cookie”。

cookie 是由服务器发送的名称/值对（使用`Set-Cookie：`头）以存储在客户端，并且然后在请求中再次发送，以匹配来自服务器的 cookie 时指定的主机和路径要求（使用`Cookie：`头）。在当今的现代网络中，网站有时会使用大量的 cookie。

## cookie 引擎

当您为特定的 easy 句柄启用“cookie 引擎”时，这意味着它将记录传入的 cookie，将它们存储在与 easy 句柄关联的内存中的“cookie 存储”中，并在随后进行的 HTTP 请求中发送适当的 cookie 回来。

有两种方法可以启用 cookie 引擎：

### 启用带有读取功能的 cookie 引擎

使用`CURLOPT_COOKIEFILE`选项，请求 libcurl 从给定文件名导入 cookie 到 easy 句柄中：

```
curl_easy_setopt(easy, CURLOPT_COOKIEFILE, "cookies.txt"); 
```

一个常见的技巧是只需指定一个不存在的文件名或简单的 "" 来激活带有空白 cookie 存储的 cookie 引擎。

此选项可以设置多次，然后将读取每个给定文件。

### 启用带有写入功能的 cookie 引擎

使用`CURLOPT_COOKIEJAR`选项，请求将接收的 cookie 存储到文件中：

```
curl_easy_setopt(easy, CURLOPT_COOKIEJAR, "cookies.txt"); 
```

当以后使用`curl_easy_cleanup()`关闭 easy 句柄时，所有已知的 cookie 将写入到给定的文件中。文件格式是浏览器曾经使用的众所周知的“Netscape cookie 文件”格式。

## 设置自定义 cookie

一种更简单、更直接的方式，只需在请求中传递一组特定的 cookie，而不向 cookie 存储添加任何 cookie，甚至不激活 cookie 引擎，就是设置 `CURLOPT_COOKIE:` 参数：

```
curl_easy_setopt(easy, CURLOPT_COOKIE, "name=daniel; present=yes;"); 
```

您设置的字符串是将在 HTTP 请求中发送的原始字符串，应该是重复序列的格式为 `NAME=VALUE;` - 包括分号分隔符。

## 导入导出

cookie 内存存储可以容纳一堆 cookie，并且 libcurl 提供了非常强大的方法让应用程序与其交互。您可以设置新的 cookie，可以替换现有的 cookie，并且可以提取现有的 cookie。

### 向 cookie 存储添加 cookie

通过简单地将其传递给 curl 的 `CURLOPT_COOKIELIST` 参数，向 cookie 存储添加新 cookie。输入的格式是 cookie 文件格式中的单行，或格式化为 `Set-Cookie:` 响应头，但我们建议使用 cookie 文件样式：

```
#define SEP  "\\t"  /* Tab separates the fields */

char *my_cookie =
  "example.com"    /* Hostname */
  SEP "FALSE"      /* Include subdomains */
  SEP "/"          /* Path */
  SEP "FALSE"      /* Secure */
  SEP "0"          /* Expiry in epoch time format. 0 == Session */
  SEP "foo"        /* Name */
  SEP "bar";       /* Value */

curl_easy_setopt(curl, CURLOPT_COOKIELIST, my_cookie); 
```

如果给定的 cookie 与已存在的 cookie 匹配（具有相同的域和路径等），它将使用新内容覆盖旧的 cookie。

### 从 cookie 存储中获取所有 cookie

有时，在关闭句柄时写入 cookie 文件并不足够，那么您的应用程序可以选择像这样从存储中提取当前已知的所有 cookie：

```
struct curl_slist *cookies
curl_easy_getinfo(easy, CURLINFO_COOKIELIST, &cookies); 
```

这将返回一个指向 cookie 链表的指针，每个 cookie （再次）指定为 cookie 文件格式的单行。列表已为您分配，因此在应用程序完成处理信息时不要忘记调用 `curl_slist_free_all`。

### Cookie 存储命令

如果设置和提取 cookie 不够，您还可以以更多方式干扰 cookie 存储：

使用以下方式清除整个内存存储区：

```
curl_easy_setopt(curl, CURLOPT_COOKIELIST, "ALL"); 
```

从内存中删除所有会话 cookie（没有到期日期的 cookie）：

```
curl_easy_setopt(curl, CURLOPT_COOKIELIST, "SESS"); 
```

强制将所有 cookie 写入之前用 `CURLOPT_COOKIEJAR` 指定的文件名：

```
curl_easy_setopt(curl, CURLOPT_COOKIELIST, "FLUSH"); 
```

强制从之前用 `CURLOPT_COOKIEFILE` 指定的文件名重新加载 cookie：

```
curl_easy_setopt(curl, CURLOPT_COOKIELIST, "RELOAD"); 
```

## Cookie 文件格式

cookie 文件格式是基于文本的，每行存储一个 cookie。以 `#` 开头的行被视为注释。

每行指定单个 cookie 的行由七个文本字段组成，用 TAB 字符分隔。

| 字段 | 示例 | 含义 |
| --- | --- | --- |
| 0 | example.com | 域名 |
| 1 | FALSE | 包括子域布尔值 |
| 2 | /foobar/ | 路径 |
| 3 | FALSE | 通过安全传输设置 |
| 4 | 1462299217 | 到期时间 - 自 1970 年 1 月 1 日以来的秒数，或 0 |
| 5 | person | cookie 的名称 |
| 6 | daniel | cookie 的值 |

# 下载

## libcurl HTTP 下载

当 HTTP URL 被请求时，且没有特定的其他方法被要求时，GET 方法是 libcurl 使用的默认方法。它向服务器请求特定资源 - 标准的 HTTP 下载请求：

```
easy = curl_easy_init();
curl_easy_setopt(easy, CURLOPT_URL, "http://example.com/");
curl_easy_perform(easy); 
```

由于在 easy 句柄中设置的选项是黏性的，并且保持不变直到更改，因此在某些情况下，您可能已经请求了另一种请求方法而不是 GET，然后希望为随后的请求切换回 GET。为此，有 `CURLOPT_HTTPGET` 选项：

```
curl_easy_setopt(easy, CURLOPT_HTTPGET, 1L); 
```

### 也下载头部

HTTP 传输还包括一组响应头。响应头是与实际有效载荷（称为响应体）相关联的元数据。所有下载也将获得一组头部，但是使用 libcurl 时，您可以选择是否要下载（查看）它们。

您可以要求 libcurl 将头部传递到与常规主体相同的“流”中，方法是使用 `CURLOPT_HEADER`：

```
easy = curl_easy_init();
curl_easy_setopt(easy, CURLOPT_HEADER, 1L);
curl_easy_setopt(easy, CURLOPT_URL, "http://example.com/");
curl_easy_perform(easy); 
```

或者您可以选择将头部存储在单独的下载文件中，依赖于 write 和 header 回调 的默认行为：

```
easy = curl_easy_init();
FILE *file = fopen("headers", "wb");
curl_easy_setopt(easy, CURLOPT_HEADERDATA, file);
curl_easy_setopt(easy, CURLOPT_URL, "http://example.com/");
curl_easy_perform(easy);
fclose(file); 
```

如果您只想随意浏览头部，甚至可以在开发时仅设置详细模式，因为这将显示发送到 stderr 的出站和入站头部：

```
curl_easy_setopt(easy, CURLOPT_VERBOSE, 1L); 
```

# 上传

## HTTP 上传

通过 HTTP 进行上传可以采用多种不同的方式，重要的是要注意它们之间的区别。它们可以使用不同的方法，比如 POST 或 PUT，在使用 POST 时，请求体的格式可能会有所不同。

除了这些 HTTP 差异之外，libcurl 还提供了不同的方法来提供要上传的数据。

### HTTP POST

POST 通常是将数据传递给远程 Web 应用程序的 HTTP 方法。在浏览器中做到这一点的一种非常常见的方法是填写 HTML 表单并按提交按钮。这是 HTTP 请求向服务器传递数据的标准方式。使用 libcurl，您通常将数据提供为指针和长度：

```
curl_easy_setopt(easy, CURLOPT_POSTFIELDS, dataptr);
curl_easy_setopt(easy, CURLOPT_POSTFIELDSIZE, (long)datalength); 
```

或者您告诉 libcurl 这是一个 post 请求，但更希望 libcurl 通过使用常规的 read 回调 获取数据：

```
curl_easy_setopt(easy, CURLOPT_POST, 1L);
curl_easy_setopt(easy, CURLOPT_READFUNCTION, read_callback); 
```

这个“普通”的 POST 还会设置请求头 `Content-Type: application/x-www-form-urlencoded`。

### HTTP 多部分表单提交

多部分表单提交仍然使用相同的 HTTP 方法 POST；不同之处仅在于请求体的格式。多部分表单提交基本上是一系列由 MIME 样式边界字符串分隔的独立的“部分”。您可以发送的部分数量没有限制。

每个这样的部分都有一个名称、一组头部和一些其他属性。

libcurl 提供了一个方便的函数来构造这样一系列部分，并将其发送到服务器。`curl_formadd` 是用于构建表单提交的函数。为每个部分调用它一次，并向其传递关于该部分的具体和特征的参数。当您添加了要发送的所有部分后，像这样传递由 `curl_formadd` 返回的句柄：

```
curl_easy_setopt(easy, CURLOPT_HTTPPOST, formposthandle); 
```

### HTTP PUT

待定
