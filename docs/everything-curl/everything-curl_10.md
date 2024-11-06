# libcurl 基础知识

# libcurl 基础知识

curl 命令行工具中的引擎是 libcurl。 libcurl 也是今天数千种工具、服务和应用程序中的引擎，执行其互联网数据传输。

## C API

libcurl 是提供了 C API 的函数库，用于使用 C 编写的应用程序。您也可以轻松地从 C++ 中使用它，只需考虑几个问题（请参阅 libcurl for C++ programmers）。对于其他语言，存在“绑定”，它们作为 libcurl 库和您喜欢的特定语言的相应函数之间的中间层工作。

## 传输导向型

我们设计 libcurl 通常是以传输为导向的，而不是强迫用户成为协议专家，或者实际上对网络或所涉及的协议了解很多。您设置传输时尽可能多的细节和特定信息，然后告诉 libcurl 执行该传输。

话虽如此，网络和协议是充满许多陷阱和特殊情况的领域，所以您对这些事物的了解越多，您就越能够理解 libcurl 的选项和工作方式。更不用说，当您进行调试并需要理解当事情不按您打算的方式进行时下一步该怎么做时，这样的知识是无价的。

最基本的 libcurl 使用应用程序可能只有几行代码，但大多数应用程序当然需要比那更多的代码。

## 默认简单，按需更多

libcurl 通常通过默认方式进行简单和基本的传输，如果您想添加更多高级功能，则通过设置正确的选项来添加。例如，libcurl 默认情况下不支持 HTTP cookies，但一旦您告诉它，它就支持了。

这使得 libcurl 的行为更容易猜测和依赖，并且也使得维护旧行为并添加新功能更容易。只有实际请求并使用新功能的应用程序才会获得该行为。

# Easy 句柄

## Easy 句柄

您需要使用 libcurl 学习的基本原理：

首先，您创建一个“easy 句柄”，这实际上是您对传输的句柄：

```
CURL *easy_handle = curl_easy_init(); 
```

然后，您在该句柄中设置各种选项以控制即将进行的传输。比如，这个示例设置了 URL：

```
/* set URL to operate on */
res = curl_easy_setopt(easy_handle, CURLOPT_URL, "http://example.com/"); 
```

创建 easy 句柄并在其上设置选项不会导致任何传输发生，并且通常甚至不会有更多事情发生，除了 libcurl 存储您希望稍后在传输实际发生时使用的内容。输入的大量语法检查和验证也可能被延迟执行，因此仅因为 `curl_easy_setopt` 没有抱怨，并不意味着输入是正确和有效的；您可能会在以后收到错误返回。

在其单独的章节中阅读更多有关 easy 选项的信息。

所有选项都是“粘性”的。它们会保持在句柄中，直到您再次更改它们，或在句柄上调用`curl_easy_reset()`。

当您设置了要传输的 easy 句柄的选项后，您就可以开始实际传输。

实际的"执行传输阶段"可以通过不同的方式和函数调用来完成，具体取决于您的应用程序中需要的行为以及 libcurl 如何最好地集成到您的架构中。这些稍后在本章中进一步描述。

传输完成后，您可以确定是否成功，还可以从 easy 句柄中提取 libcurl 在传输过程中收集的统计信息和各种信息。请参阅传输后信息。

在传输进行时，libcurl 会调用您指定的函数—称为*回调*—来传递数据，读取数据或执行各种操作。

### 复用！

easy 句柄旨在被重复使用和设计。当您使用 easy 句柄进行单个传输后，您可以立即再次使用它进行下一次传输。这样做可以获得很多好处。

# 驱动传输

### "驱动"传输

libcurl 提供三种不同的传输方式。在您的情况下使用哪种方式完全取决于您的需求。

1.  'easy'接口允许您以同步方式进行单个传输。当传输完成时，libcurl 将完成整个传输并将控制权返回给您的应用程序—无论成功与否。

1.  'multi'接口用于同时进行多个传输，或者您只想要一个非阻塞传输。

1.  'multi_socket'接口是常规 multi 接口的轻微变体，但是基于事件，并且如果您打算将同时传输的数量扩展到数百或数千个，这确实是建议使用的 API。

让我们更仔细地看看每一个...

# 使用 easy 进行驱动

### 使用 easy 接口进行驱动

名称'easy'之所以被选中，只是因为这确实是使用 libcurl 的简单方式，当然，简单也意味着一些限制。比如，它一次只能进行一次传输，并且它在单个函数调用中完成整个传输，一旦完成就返回：

```
res = curl_easy_perform( easy_handle ); 
```

如果服务器很慢，传输很大，或者网络中存在一些不愉快的超时等情况，这个函数调用可能需要很长时间。当然，您可以设置超时时间，不允许它花费超过 N 秒，但根据特定条件，这仍可能意味着相当长的时间。

如果您希望在 libcurl 使用 easy 接口进行传输时，应用程序执行其他操作，您需要使用多个线程。如果您希望在使用 easy 接口时进行多个同时传输，您需要在各自的线程中执行每个传输。

# 使用 multi 进行驱动

### 使用 multi 接口进行驱动

名称'multi'是指多个，即多个并行传输，全部在同一个单线程中完成。multi API 是非阻塞的，因此对于单个传输也可以使用它。

传输仍然设置在一个"easy" `CURL *`句柄中，如上所述，但是使用多接口时，您还需要创建一个多`CURLM *`句柄并使用它来驱动所有单个传输。多句柄可以"持有"一个或多个易句柄：

```
CURLM *multi_handle = curl_multi_init(); 
```

多句柄还可以设置某些选项，您可以使用`curl_multi_setopt()`来设置，但在最简单的情况下，您可能没有任何需要设置的内容。

要进行多接口传输，首先需要将所有应该传输到多句柄的单个易句柄添加到其中。您可以在任何时候将它们添加到多句柄中，并且可以在任何时候将它们移除。从多句柄中移除一个易句柄将会移除关联，特定的传输将立即停止。

将易句柄添加到多句柄非常容易：

```
curl_multi_add_handle( multi_handle, easy_handle ); 
```

移除一个易句柄同样容易：

```
curl_multi_remove_handle( multi_handle, easy_handle ); 
```

添加了代表您要执行的传输的易句柄后，您编写传输循环。使用多接口，您进行循环，这样您可以向 libcurl 询问一组文件描述符和一个超时值，并自己进行`select()`调用，或者您可以使用稍微简化的版本，它会为我们执行这些操作，使用`curl_multi_wait`。最简单的循环基本上是这样的：（*请注意，真实应用程序应检查返回代码*）

```
int transfers_running;
do {
   curl_multi_wait ( multi_handle, NULL, 0, 1000, NULL);
   curl_multi_perform ( multi_handle, &transfers_running );
} while (transfers_running); 
```

`curl_multi_wait`的第四个参数，在上面的示例中设置为 1000，是以毫秒为单位的超时时间。这是函数在返回之前等待任何活动的最长时间。在再次调用`curl_multi_perform`之前不要等待太长时间，因为存在超时、进度回调等，如果这样做可能会失去精度。

要改为在我们自己上执行 select()，我们从 libcurl 中提取文件描述符和超时值，如下所示（*请注意，真实应用程序应检查返回代码*）：

```
int transfers_running;
do {
  fd_set fdread;
  fd_set fdwrite;
  fd_set fdexcep;
  int maxfd = -1;
  long timeout;

  /* extract timeout value */
  curl_multi_timeout(multi_handle, &timeout);
  if (timeout < 0)
    timeout = 1000;

  /* convert to struct usable by select */
  timeout.tv_sec = timeout / 1000;
  timeout.tv_usec = (timeout % 1000) * 1000;

  FD_ZERO(&fdread);
  FD_ZERO(&fdwrite);
  FD_ZERO(&fdexcep);

  /* get file descriptors from the transfers */
  mc = curl_multi_fdset(multi_handle, &fdread, &fdwrite, &fdexcep, &maxfd);

  if (maxfd == -1) {
    SHORT_SLEEP;
  }
  else
   select(maxfd+1, &fdread, &fdwrite, &fdexcep, &timeout);

  /* timeout or readable/writable sockets */
  curl_multi_perform(multi_handle, &transfers_running);
} while ( transfers_running ); 
```

这两个循环都让您可以使用一个或多个自己的文件描述符进行等待，就像如果您从自己的套接字或管道等读取一样。

而且，您可以在循环期间的任何时候添加和移除易句柄到多句柄。在传输过程中移除句柄将中止该传输。

## 何时完成单个传输？

如上面的示例所示，程序可以通过观察`transfers_running`变量减少来检测单个传输何时完成。

它还可以调用`curl_multi_info_read()`，如果传输已结束，它将返回指向一个结构体（一个"消息"）的指针，然后您可以使用该结构体了解该传输的结果。

当您进行多个并行传输时，当然可以在同一次`curl_multi_perform`调用中完成多个传输，然后您可能需要多次调用`curl_multi_info_read`来获取每个已完成传输的信息。

# 使用 multi_socket 进行驱动

## 使用"multi_socket"接口进行驱动

multi_socket 是常规多接口的额外辣味版本，专为事件驱动的应用程序设计。确保你先阅读 使用多接口进行驱动 部分。

multi_socket 支持多个并行传输——全部在同一个单线程中完成——并且已被用来在单个应用程序中运行数万次传输。如果你进行大量（>100 或更多）的并行传输，这通常是最合理的 API。

这种情况下的事件驱动意味着你的应用程序使用了一个系统级库或设置，它“订阅”了一些套接字，并在其中一个套接字可读或可写时通知你的应用程序，还会告诉你具体是哪个套接字。

这种设置允许客户端将同时传输的数量扩展到比其他系统更高，并且仍然保持良好的性能。否则，“常规”API 会浪费大量时间扫描所有套接字列表。

## 选择一个

有很多事件驱动系统可供选择，而 libcurl 完全不关心你使用哪一个。libevent、libev 和 libuv 是三个流行的选项，但你也可以直接使用操作系统的本地解决方案，如 epoll、kqueue、/dev/poll、pollset、事件完成或 I/O 完成端口。

## 许多 easy 句柄

就像常规多接口一样，你可以使用 `curl_multi_add_handle()` 将 easy 句柄添加到多句柄中。每个传输都需要一个 easy 句柄。

你可以在传输运行时随时添加它们，也可以使用 `curl_multi_remove_handle` 调用类似地随时移除 easy 句柄。不过通常情况下，只有在传输完成后才会移除句柄。

## 多套接字回调

如上所述，这种基于事件的机制依赖于应用程序知道 libcurl 使用的是哪些套接字，以及 libcurl 在这些套接字上等待什么：如果它等待套接字变为可读、可写或两者兼具！

它还需要告诉 libcurl 其超时时间已过，因为它负责驱动一切 libcurl 不能自己做。所以 libcurl 必须告诉应用程序一个更新的超时值。

### 套接字回调

libcurl 通过一个称为 [CURLMOPT_SOCKETFUNCTION](https://curl.haxx.se/libcurl/c/CURLMOPT_SOCKETFUNCTION.html) 的回调来通知应用程序有关待等待的套接字活动。你的应用程序需要实现这样一个函数：

```
int socket_callback(CURL *easy,      /* easy handle */
                    curl_socket_t s, /* socket */
                    int what,        /* what to wait for */
                    void *userp,     /* private callback pointer */
                    void *socketp)   /* private socket pointer */
{
   /* told about the socket 's' */
}

/* set the callback in the multi handle */
curl_multi_setopt(multi_handle, CURLMOPT_SOCKETFUNCTION, socket_callback); 
```

使用这种方式，libcurl 将设置和移除你的应用程序应该监视的套接字。你的应用程序告诉底层事件驱动系统等待这些套接字。如果有多个套接字需要等待，这个回调将被多次调用，并且当状态发生变化时可能需要从等待可写的套接字切换为等待可读的套接字。

当应用程序正在监视的其中一个套接字注册为可读或可写时，如请求的，您通过调用 `curl_multi_socket_action()` 并传入受影响的套接字和指定已注册的套接字活动的关联位掩码来告诉 libcurl：

```
int running_handles;
ret = curl_multi_socket_action(multi_handle,
                               sockfd, /* the socket with activity */
                               ev_bitmask, /* the specific activity */
                               &running_handles); 
```

### timer_callback

应用程序控制并等待套接字活动。但即使没有套接字活动，libcurl 也有事情要做。超时事务，调用进度回调，重新开始重试或失败超时的传输等。为了使其工作，应用程序还必须确保处理 libcurl 设置的单次超时。

libcurl 使用 timer_callback [CURLMOPT_TIMERFUNCTION](https://curl.haxx.se/libcurl/c/CURLMOPT_TIMERFUNCTION.html) 来设置超时：

```
int timer_callback(multi_handle,   /* multi handle */
                   timeout_ms,     /* milliseconds to wait */
                   userp)          /* private callback pointer */
{
  /* the new time-out value to wait for is in 'timeout_ms' */
}

/* set the callback in the multi handle */
curl_multi_setopt(multi_handle, CURLMOPT_TIMERFUNCTION, timer_callback); 
```

整个多 handle 只有一个超时需要应用程序处理，无论已添加了多少个单独的 easy handle 或正在进行多少个传输。定时器回调将被更新为当前最接近的等待时间段。如果因为套接字活动而在超时到期时间之前调用了 libcurl，它很可能会在它到期之前再次更新超时值。

当您选择的事件系统最终告诉您计时器已到期时，您需要告诉 libcurl：

```
curl_multi_socket_action(multi, CURL_SOCKET_TIMEOUT, 0, &running); 
```

…在许多情况下，这将使 libcurl 再次调用 timer_callback 并设置下一个到期周期的新超时。

### 如何开始一切

当您将一个或多个 easy handle 添加到多 handle 并在多 handle 中设置套接字和计时器回调后，您就可以开始传输了。

要开始一切，您告诉 libcurl 它超时了（因为所有的 easy handle 都是从非常非常短的超时时间开始的），这将使 libcurl 调用回调函数来设置事物，并从此你可以让你的事件系统驱动：

```
/* all easy handles and callbacks are setup */

curl_multi_socket_action(multi, CURL_SOCKET_TIMEOUT, 0, &running);

/* now the callbacks should have been called and we have sockets to wait for
   and possibly a timeout, too. Make the event system do its magic */

event_base_dispatch(event_base); /* libevent2 has this API */

/* at this point we have exited the event loop */ 
```

### 什么时候完成？

由 `curl_multi_socket_action` 返回的 'running_handles' 计数器保存了当前尚未完成的传输数量。当该数字达到零时，我们知道没有传输正在进行。

每当 'running_handles' 计数器更改时，`curl_multi_info_read()` 将返回有关已完成的特定传输的信息。

# 连接重用

# 连接重用

libcurl 保持一组旧连接保持活动状态。当一个传输完成时，它将在一个“连接池”中保持 N 个连接活动（有时也称为连接缓存），以便后续传输能够重用其中一个现有连接而不是创建新连接。重用连接而不是创建新连接在速度和所需资源方面提供了显著的好处。

当 libcurl 准备为传输建立新连接时，它将首先检查是否有现有连接可重用。连接重用检查在使用任何 DNS 或其他名称解析机制之前进行，因此它完全基于主机名。如果存在到正确主机名的现有活动连接，则还将检查很多其他属性（端口号、协议等）以确保可以使用。

## 易 API 连接池

当您使用易 API，或者更具体地说，`curl_easy_perform()` 时，libcurl 将保持与特定易句柄关联的池。然后重用相同的易句柄将确保它可以重用其连接。

## 多 API 连接池

当您使用多 API 时，连接池将与多句柄关联。这样可以自由清理和重新创建易句柄，而不必担心丢失连接池，并且可以使一个易句柄使用的连接在以后的传输中被另一个易句柄重用。只需重用多句柄！

## 共享“连接缓存”

自 libcurl 7.57.0 开始，应用程序可以使用共享接口来共享相同的连接池，否则它们是独立的传输。

# 回调函数

## 回调函数

libcurl 内有很多操作是通过*回调*来控制的。回调是提供给 libcurl 的函数指针，libcurl 在某个时刻调用它以完成特定的工作。

每个回调都有其特定的文档化目的，并且要求您用精确的函数原型编写它，以接受正确的参数并返回文档化的返回代码和返回值，以便 libcurl 表现出您希望的方式。

每个回调选项还有一个关联的“用户指针”伴侣选项。这个用户指针是 libcurl 不会触及或关心的指针，但只是作为参数传递给回调。这使您可以将指针传递到本地数据，一直到回调函数。

除非在 libcurl 函数文档中明确说明，否则不得在 libcurl 回调函数中调用 libcurl 函数。

# 写数据

### 写回调

写回调由 `CURLOPT_WRITEFUNCTION` 设置：

```
curl_easy_setopt(handle, CURLOPT_WRITEFUNCTION, write_callback); 
```

`write_callback` 函数必须与此原型匹配：

```
size_t write_callback(char *ptr, size_t size, size_t nmemb, void *userdata); 
```

此回调函数会在 libcurl 收到需要保存的数据时立即被调用。*ptr* 指向传递的数据，该数据的大小为 *size* 乘以 *nmemb*。

如果未设置此回调，则 libcurl 默认使用 'fwrite'。

写入回调将尽可能传递尽可能多的数据，但不得做出任何假设。它可能是一个字节，也可能是数千个字节。将传递给写入回调的主体数据的最大量在 curl.h 头文件中定义：`CURL_MAX_WRITE_SIZE`（通常默认为 16KB）。如果为此传输启用了`CURLOPT_HEADER`，使得头数据传递给写入回调，您可以获得最多`CURL_MAX_HTTP_HEADER`字节的头数据传递给它。这通常意味着 100KB。

如果传输的文件为空，此函数可能会以零字节数据调用。

传递给此函数的数据不会以零结尾！例如，您不能使用 printf 的“％s”运算符显示内容，也不能使用 strcpy 复制它。

此回调函数应返回实际处理的字节数。如果该数字与传递给回调函数的数字不同，它将向库发出错误信号。这将导致传输中止，并且使用的 libcurl 函数将返回`CURLE_WRITE_ERROR`。

传递给回调函数中*userdata*参数的用户指针是使用`CURLOPT_WRITEDATA`设置的：

```
curl_easy_setopt(handle, CURLOPT_WRITEDATA, custom_pointer); 
```

# 读取数据

### 读取回调

读取回调函数是通过`CURLOPT_READFUNCTION`设置的：

```
curl_easy_setopt(handle, CURLOPT_READFUNCTION, read_callback); 
```

`read_callback`函数必须匹配此原型：

```
size_t read_callback(char *buffer, size_t size, size_t nitems, void *stream); 
```

当 libcurl 希望将数据发送到服务器时，将调用此回调函数。这是您设置的用于上传数据或以其他方式将其发送到服务器的传输。此回调将一遍又一遍地调用，直到所有数据已传递或传输失败。

**stream**指针指向使用`CURLOPT_READDATA`设置的私有数据：

```
curl_easy_setopt(handle, CURLOPT_READDATA, custom_pointer); 
```

如果未设置此回调函数，libcurl 将默认使用'fread'。

指针**buffer**指向的数据区域应由您的函数用最多**size**乘以**nitems**字节数填充。然后，回调应返回存储在该内存区域中的字节数，如果已达到数据的末尾，则返回 0。回调还可以返回一些“魔术”返回代码，以立即导致 libcurl 立即返回失败或暂停特定传输。有关详细信息，请参阅[CURLOPT_READFUNCTION man page](https://curl.haxx.se/libcurl/c/CURLOPT_READFUNCTION.html)。

# 进度信息

### 进度回调

进度回调是在整个传输的整个生命周期中定期和重复地为每个传输调用的。旧的回调是使用`CURLOPT_PROGRESSFUNCTION`设置的，但现代和首选的回调是使用`CURLOPT_XFERINFOFUNCTION`设置的：

```
curl_easy_setopt(handle, CURLOPT_XFERINFOFUNCTION, xfer_callback); 
```

`xfer_callback`函数必须匹配此原型：

```
int xfer_callback(void *clientp, curl_off_t dltotal, curl_off_t dlnow,
                  curl_off_t ultotal, curl_off_t ulnow); 
```

如果设置了此选项，并且`CURLOPT_NOPROGRESS`设置为 0（零），则 libcurl 会以频繁的间隔调用此回调函数。在数据传输时，它将被非常频繁地调用，而在没有传输任何内容时，它可能会减慢到每秒约一次的速度。

**clientp** 指针指向使用 `CURLOPT_XFERINFODATA` 设置的私有数据：

```
curl_easy_setopt(handle, CURLOPT_XFERINFODATA, custom_pointer); 
```

回调会告知 libcurl 将传输和已传输的数据量，以字节数表示：

+   **dltotal** 是 libcurl 预计在此传输中下载的总字节数。

+   **dlnow** 是迄今为止已下载的字节数。

+   **ultotal** 是 libcurl 预计在此传输中上传的总字节数。

+   **ulnow** 是迄今为止已上传的字节数。

传递给回调的未知/未使用的参数值将设置为零（例如，如果您只下载数据，则上传大小将保持为 0）。许多时候，回调将在知道数据大小之前首先调用一次或多次，因此必须编写程序来处理这种情况。

从此回调返回非零值将导致 libcurl 中止传输并返回 `CURLE_ABORTED_BY_CALLBACK`。

如果您使用多接口传输数据，则在空闲期间不会调用此函数，除非您调用执行传输的适当的 libcurl 函数。

（已弃用的回调 `CURLOPT_PROGRESSFUNCTION` 的工作方式相同，但它使用 `double` 类型的参数而不是 `curl_off_t`。）

# 头数据

### 头回调

头回调函数设置为 `CURLOPT_HEADERFUNCTION`：

```
curl_easy_setopt(handle, CURLOPT_HEADERFUNCTION, header_callback); 
```

`header_callback` 函数必须匹配此原型：

```
size_t header_callback(char *ptr, size_t size, size_t nmemb, void *userdata); 
```

此回调函数在 libcurl 收到头后立即被调用。*ptr* 指向传递的数据，该数据的大小为 *size* 乘以 *nmemb*。libcurl 缓冲头并仅将“完整”头逐个传递给此回调。

传递给此函数的数据将不以零结尾！例如，您不能使用 printf 的 "%s" 运算符显示内容，也不能使用 strcpy 复制它。

此回调函数应返回实际处理的字节数。如果该数字与传递给回调函数的数字不同，这将向库发出错误信号。这将导致传输中止，并且使用的 libcurl 函数将返回 `CURLE_WRITE_ERROR`。

传递给回调函数的用户指针在 *userdata* 参数中设置为 `CURLOPT_HEADERDATA`：

```
curl_easy_setopt(handle, CURLOPT_HEADERDATA, custom_pointer); 
```

# 调试

### 调试回调

调试回调函数设置为 `CURLOPT_DEBUGFUNCTION`：

```
curl_easy_setopt(handle, CURLOPT_DEBUGFUNCTION, debug_callback); 
```

`debug_callback` 函数必须匹配此原型：

```
int debug_callback(CURL *handle,
                   curl_infotype type,
                   char *data,
                   size_t size,
                   void *userdata); 
```

此回调函数替换库中的默认详细输出函数，并将为所有调试和跟踪消息调用以帮助应用程序了解发生了什么。*type* 参数解释提供的数据类型：头、数据或 SSL 数据以及流动方向。

此回调的常见用途是获取 libcurl 发送和接收的所有数据的完整跟踪。发送到此回调的数据始终是未加密版本，即使例如使用 HTTPS 或其他加密协议时也是如此。

此回调必须返回零或导致传输停止并带有错误代码。

回调中传入的*userdata*参数中的用户指针是使用`CURLOPT_DEBUGDATA`设置的：

```
curl_easy_setopt(handle, CURLOPT_DEBUGDATA, custom_pointer); 
```

# sockopt

### sockopt 回调

使用`CURLOPT_SOCKOPTFUNCTION`设置 sockopt 回调：

```
curl_easy_setopt(handle, CURLOPT_SOCKOPTFUNCTION, sockopt_callback); 
```

`sockopt_callback`函数必须匹配此原型：

```
int sockopt_callback(void *clientp,
                     curl_socket_t curlfd,
                     curlsocktype purpose); 
```

当新套接字被创建但在连接调用之前，此回调函数由 libcurl 调用，以允许应用程序更改特定套接字选项。

**clientp**指针指向使用`CURLOPT_SOCKOPTDATA`设置的私有数据：

```
curl_easy_setopt(handle, CURLOPT_SOCKOPTDATA, custom_pointer); 
```

此回调应返回：

+   成功时返回 CURL_SOCKOPT_OK

+   CURL_SOCKOPT_ERROR 用于向 libcurl 发出不可恢复的错误信号

+   CURL_SOCKOPT_ALREADY_CONNECTED 表示成功，但套接字实际上已连接到目的地

# SSL 上下文

### SSL 上下文回调

待定

# 寻找和 ioctl

### 寻找和 ioctl 回调

待定

# 网络数据转换

### 转换为网络回调和从网络回调

待定

### 转换为 UTF-8 回调

待定

# 打开套接字和关闭套接字

# 打开套接字和关闭套接字回调

有时您会遇到这样的情况，您希望应用程序更精确地控制 libcurl 将用于其操作的套接字。libcurl 提供了一对回调函数，用于替换 libcurl 自己对`socket()`的调用和随后对相同文件描述符的`close()`。

## 提供一个文件描述符

通过设置`CURLOPT_OPENSOCKETFUNCTION`回调，您可以提供一个自定义函数来返回 libcurl 使用的文件描述符：

```
curl_easy_setopt(handle, CURLOPT_OPENSOCKETFUNCTION, opensocket_callback); 
```

`opensocket_callback`函数必须匹配此原型：

```
curl_socket_t opensocket_callback(void *clientp,
                                  curlsocktype purpose,
                                  struct curl_sockaddr *address); 
```

回调函数的第一个参数是*clientp*，它只是您使用`CURLOPT_OPENSOCKETDATA`设置的不透明指针。

另外两个参数传入标识套接字用于何种*目的*和*地址*的数据。*目的*是一个具有`CURLSOCKTYPE_IPCXN`或`CURLSOCKTYPE_ACCEPT`值的 typedef，基本上标识套接字在哪种情况下被创建。当 libcurl 用于接受传入的 FTP 连接时，"accept"情况是 FTP 主动模式使用时，而所有其他情况下，当 libcurl 为自己的出站连接创建套接字时，传入*IPCXN*值。

*address*指针指向描述创建此套接字的网络目的地的 IP 地址的`struct curl_sockaddr`。例如，您的回调可以使用此信息来列入白名单或黑名单特定地址或地址范围。

socketopen 回调也明确允许修改该结构中的目标地址，如果您想提供某种网络过滤器或转换层。

回调应返回一个文件描述符或`CURL_SOCKET_BAD`，这将导致 libcurl 内部发生不可恢复的错误，并最终从其执行函数返回`CURLE_COULDNT_CONNECT`。

如果要返回一个*已连接*到服务器的文件描述符，则还必须设置 sockopt 回调并确保返回正确的返回值。

`curl_sockaddress`结构如下：

```
struct curl_sockaddr {
  int family;
  int socktype;
  int protocol;
  unsigned int addrlen;
  struct sockaddr addr;
}; 
```

## 套接字关闭回调

与打开套接字对应的回调当然是关闭套接字。通常，当您提供一种自定义方式来提供文件描述符时，您也希望提供自己的清理版本：

```
curl_easy_setopt(handle, CURLOPT_CLOSEOCKETFUNCTION, closesocket_callback); 
```

`closesocket_callback`函数必须匹配此原型：

```
int closesocket_callback(void *clientp, curl_socket_t item); 
```

# SSH 密钥

### SSH 密钥回调

待定

# RTSP 交错数据

### RTSP 交错回调

待定

# FTP 匹配

### FTP 块回调

待定

### FTP 匹配回调

待定

# 清理

## 清理

在前面的部分中，我们已经讨论了如何设置句柄以及如何驱动传输。所有传输当然最终都会在某个时刻结束，无论是成功还是失败。

### 多 API

当您使用多 API 完成单个传输时，您可以使用`curl_multi_info_read()`来确定确切完成的 easy 句柄，并使用`curl_multi_remove_handle()`从多句柄中删除该 easy 句柄。

如果从多句柄中删除最后一个 easy 句柄，以便没有更多的传输正在进行，您可以像这样关闭多句柄：

```
curl_multi_cleanup( multi_handle ); 
```

### easy 句柄

当 easy 句柄完成其用途时，您可以关闭它。但是，如果您打算进行另一个传输，则建议您更好地重用句柄，而不是关闭它并创建一个新的句柄。

如果您不打算使用 easy 句柄进行另一个传输，您只需要求 libcurl 清理：

```
curl_easy_cleanup( easy_handle ); 
```

# 名称解析

# 名称解析

libcurl 可以执行的大多数传输都涉及首先将名称转换为互联网地址。这就是"名称解析"。直接在 URL 中使用数字 IP 地址通常可以避免名称解析阶段，但在许多情况下，手动用 IP 地址替换名称并不容易。

libcurl 非常努力地尝试重用现有连接而不是创建新连接。检查要使用的现有连接的函数纯粹基于名称，并且在尝试任何名称解析之前执行。这就是重用如此快速的原因之一。使用重用连接的传输不会再次解析主机名。

如果无法重用连接，则 libcurl 将主机名解析为其解析到的地址集。通常，这意味着请求 IPv4 和 IPv6 地址，并且可能会有一整套这些地址返回给 libcurl。然后尝试该地址集，直到找到一个有效的地址，否则返回失败。

应用程序可以通过将`CURLOPT_IPRESOLVE`设置为首选值，强制 libcurl 仅使用 IPv4 或 IPv6 解析的地址。例如，要求仅使用 IPv6 地址：

```
curl_easy_setopt(easy, CURLOPT_IPRESOLVE, CURL_IPRESOLVE_V6); 
```

## 名称解析器后端

libcurl 可以以至少三种不同的方式构建名称解析，并根据使用的后端方式，它会获得略有不同的功能集，并有时会修改行为。

1.  默认后端是在新的辅助线程中调用“正常”的 libc 解析器函数，以便如果需要，仍然可以进行细粒度的超时，并且不涉及阻塞调用。

1.  在旧系统上，libcurl 使用标准同步名称解析函数。不幸的是，在其操作期间，它会使多句柄内的所有传输都阻塞，并且很难进行良好的超时处理。

1.  还支持使用 c-ares 第三方库进行解析，该库支持异步名称解析而无需使用线程。这对于大量并行传输更具扩展性，但并不总是与本机名称解析功能完全兼容。

## 缓存

当名称已解析时，结果将放入 libcurl 的内存缓存中，以便对相同名称的后续解析几乎瞬间完成，只要名称保留在 DNS 缓存中。默认情况下，每个条目在缓存中保留 60 秒，但该值可以使用`CURLOPT_DNS_CACHE_TIMEOUT`进行更改。

当使用`curl_easy_perform`时，DNS 缓存保留在 easy 句柄内，或者当使用多接口时，保留在多句柄内。还可以使用共享接口在多个 easy 句柄之间共享。

## 主机的自定义地址

有时，提供“虚假”地址给真实主机名是很方便的，这样 libcurl 将连接到不同的地址，而不是实际名称解析所建议的地址。

借助[CURLOPT_RESOLVE](https://curl.haxx.se/libcurl/c/CURLOPT_RESOLVE.html)选项的帮助，应用程序可以预先填充 libcurl 的 DNS 缓存，为给定的主机名和端口号提供自定义地址。

要使 libcurl 连接到 127.0.0.1，当请求端口 443 的 example.com 时，应用程序可以执行以下操作：

```
struct curl_slist *dns;
dns = curl_slist_append(NULL, "example.com:443:127.0.0.1");
curl_easy_setopt(curl, CURLOPT_RESOLVE, dns); 
```

由于这将“虚假”地址放入 DNS 缓存中，即使在跟随重定向等情况下也能正常工作。

## 名称服务器选项

对于构建使用 c-ares 的 libcurl，有一些可用的选项可以提供对要使用的 DNS 服务器以及如何使用的细粒度控制。这仅限于 c-ares 构建，因为当使用标准系统调用进行名称解析时，这些功能是不可用的。

+   使用`CURLOPT_DNS_SERVERS`，应用程序可以选择使用一组专用的 DNS 服务器。

+   使用`CURLOPT_DNS_INTERFACE`，它可以告诉 libcurl 使用哪个网络接口来进行 DNS 通信，而不是默认的接口。

+   使用`CURLOPT_DNS_LOCAL_IP4`和`CURLOPT_DNS_LOCAL_IP6`，应用程序可以指定将 DNS 解析绑定到哪些特定的网络地址。

## 全局 DNS 缓存不好

有一个*已弃用*的选项称为`CURLOPT_DNS_USE_GLOBAL_CACHE`，启用后告诉 curl 使用全局 DNS 缓存。此缓存没有锁，并在全局上下文中存储数据，然后可以由所有其他设置为使用全局缓存的 easy 句柄共享。

此选项仅应由旧版应用程序使用，您*应该*努力将其转换为使用共享接口共享 DNS 缓存的“正确”方法。此选项将在将来的版本中移除。

# 代理

# 代理

网络环境中的代理是一种中间人，即在您作为客户端和您要通信的远程服务器之间的服务器。客户端联系中间人，然后中间人再为您联系远程服务器。

这种类型的代理使用有时被公司和组织使用，此时通常要求您使用它们来访问目标服务器。

在与代理通信时有几种不同类型的代理和不同的协议可用，并且 libcurl 支持一些最常见的代理协议。重要的是要意识到，用于代理的协议未必与用于远程服务器的协议相同。

在使用 libcurl 进行传输时，您需要指出代理的服务器名称和端口号。您可能会发现，与 libcurl 相比，您喜爱的浏览器可以以略微更高级的方式执行此操作，我们将在后面的章节中详细介绍这些细节。

## 代理类型

libcurl 支持两种主要的代理类型：SOCKS 和 HTTP 代理。更具体地说，它支持带有或不带有远程名称解析的 SOCKS4 和 SOCKS5，以及本地代理的 HTTP 和 HTTPS。

指定要使用的代理类型最简单的方法是设置代理主机名字符串（`CURLOPT_PROXY`）的方案部分以匹配它：

```
socks4://proxy.example.com:12345/
socks4a://proxy.example.com:12345/
socks5://proxy.example.com:12345/
socks5h://proxy.example.com:12345/
http://proxy.example.com:12345/
https://proxy.example.com:12345/ 
```

`socks4` - 意味着带有本地名称解析的 SOCKS4

`socks4a` - 意味着带有代理名称解析的 SOCKS4

`socks5` - 意味着带有本地名称解析的 SOCKS5

`socks5h` - 意味着带有代理名称解析的 SOCKS5

`http` - 意味着 HTTP，它总是让代理解析名称

`https` - 意味着 HTTPS **到代理**，它总是让代理解析名称（请注意，HTTPS 代理支持最近添加，从 curl 7.52.0 开始，它仅在某些 TLS 库中有效：OpenSSL、GnuTLS 和 NSS。）

如果您更喜欢仅设置主机名，则还可以选择使用单独的选项设置代理的类型，使用 `CURLOPT_PROXYTYPE`。类似地，您可以使用 `CURLOPT_PROXYPORT` 设置要使用的代理端口号。

## 本地或代理名称解析

在上面的一节中，您可以看到不同的代理设置允许由传输中涉及的不同方进行名称解析。在几种情况下，您可以选择让客户端解析服务器主机名并将 IP 地址传递给代理进行连接 - 这当然假设客户端系统上的名称查找准确无误 - 或者您可以将名称交给代理来让代理解析名称；将其转换为要连接的 IP 地址。

当您使用 HTTP 或 HTTPS 代理时，您始终会将名称提供给代理来解析。

## 哪个代理？

待定

## 使用代理进行各种协议

待定

## HTTP 代理

待定

## HTTPS 代理

待定

## 代理认证

待定

# 传输后信息

# 传输后信息

记得 libcurl 传输与“easy handle”相关联！每个传输都有这样一个 handle，当一个传输完成后，在 handle 被清理或重新用于另一个传输之前，它可以用于从上一个操作中提取信息。

使用`curl_easy_getinfo()`函数，你可以获取你感兴趣的特定信息，如果可能的话，它会将该信息返回给你。

当你使用此函数时，你需要传递 easy handle、你想要的信息以及一个指向保存答案的变量的指针。你必须传递一个正确类型的变量的指针，否则可能会出现问题。这些信息值被设计为在传输完成*之后*提供。

你收到的数据可以是 long、'char *'、'struct curl_slist* '、double 或套接字。

这是你从上一个 HTTP 传输中提取`Content-Type:`值的方法：

```
CURLcode res;
char *content_type;
res = curl_easy_getinfo(curl, CURLINFO_CONTENT_TYPE, &content_type); 
```

但如果你想提取在该连接中使用的本地端口号：

```
CURLcode res;
long port_number;
res = curl_easy_getinfo(curl, CURLINFO_LOCAL_PORT, &port_number); 
```

## 可用信息

| 获取信息选项 | 类型 | 描述 |
| --- | --- | --- |
| CURLINFO_ACTIVESOCKET | curl_socket_t | 会话的活动套接字 |
| CURLINFO_APPCONNECT_TIME | double | 从开始到 SSL/SSH 握手完成的时间 |
| CURLINFO_CERTINFO | struct curl_slist * | 证书链 |
| CURLINFO_CONDITION_UNMET | long | 时间条件是否满足 |
| CURLINFO_CONNECT_TIME | double | 从开始到远程主机或代理完成的时间 |
| CURLINFO_CONTENT_LENGTH_DOWNLOAD | double | 来自 Content-Length 头部的内容长度 |
| CURLINFO_CONTENT_LENGTH_UPLOAD | double | 上传大小 |
| CURLINFO_CONTENT_TYPE | char * | 来自 Content-Type 头部的内容类型 |
| CURLINFO_COOKIELIST | struct curl_slist * | 所有已知 cookie 的列表 |
| CURLINFO_EFFECTIVE_URL | char * | 最后使用的 URL |
| CURLINFO_FILETIME | long | 检索文档的远程时间 |
| CURLINFO_FTP_ENTRY_PATH | char * | 登录到 FTP 服务器后的入口路径 |
| CURLINFO_HEADER_SIZE | long | 所有接收到的头部字节总数 |
| CURLINFO_HTTPAUTH_AVAIL | long | 可用的 HTTP 身份验证方法（位掩码） |
| CURLINFO_HTTP_CONNECTCODE | long | 最后一个代理 CONNECT 响应代码 |
| CURLINFO_HTTP_VERSION | long | 连接中使用的 HTTP 版本 |
| CURLINFO_LASTSOCKET | long | 最后使用的套接字 |
| CURLINFO_LOCAL_IP | char * | 最后一次连接的本地端 IP 地址 |
| CURLINFO_LOCAL_PORT | long | 最后一次连接的本地端口 |
| CURLINFO_NAMELOOKUP_TIME | double | 从开始到名称解析完成的时间 |
| CURLINFO_NUM_CONNECTS | long | 用于上次传输的新成功连接数 |
| CURLINFO_OS_ERRNO | long | 上次连接失败的 errno |
| CURLINFO_PRETRANSFER_TIME | double | 从开始到传输开始前的时间 |
| CURLINFO_PRIMARY_IP | char * | 上次连接的 IP 地址 |
| CURLINFO_PRIMARY_PORT | long | 上次连接的端口 |
| CURLINFO_PRIVATE | char * | 用户私有数据指针 |
| CURLINFO_PROTOCOL | long | 连接使用的协议 |
| CURLINFO_PROXYAUTH_AVAIL | long | 可用的 HTTP 代理身份验证方法 |
| CURLINFO_PROXY_SSL_VERIFYRESULT | long | 代理证书验证结果 |
| CURLINFO_REDIRECT_COUNT | long | 已跟随的重定向总数 |
| CURLINFO_REDIRECT_TIME | double | 最终传输之前所有重定向步骤所花费的时间 |
| CURLINFO_REDIRECT_URL | char * | 如果启用重定向，则重定向将带您到的 URL |
| CURLINFO_REQUEST_SIZE | long | 已发送的 HTTP 请求中的字节数 |
| CURLINFO_RESPONSE_CODE | long | 上次接收到的响应代码 |
| CURLINFO_RTSP_CLIENT_CSEQ | long | 下一个将被使用的 RTSP CSeq |
| CURLINFO_RTSP_CSEQ_RECV | long | 上次接收到的 RTSP CSeq |
| CURLINFO_RTSP_SERVER_CSEQ | long | 下一个将被期望的 RTSP CSeq |
| CURLINFO_RTSP_SESSION_ID | char * | RTSP 会话 ID |
| CURLINFO_SCHEME | char * | 连接使用的协议 |
| CURLINFO_SIZE_DOWNLOAD | double | 已下载字节数 |
| CURLINFO_SIZE_UPLOAD | double | 已上传字节数 |
| CURLINFO_SPEED_DOWNLOAD | double | 平均下载速度 |
| CURLINFO_SPEED_UPLOAD | double | 平均上传速度 |
| CURLINFO_SSL_ENGINES | struct curl_slist * | OpenSSL 加密引擎列表 |
| CURLINFO_SSL_VERIFYRESULT | long | 证书验证结果 |
| CURLINFO_STARTTRANSFER_TIME | double | 从开始到接收到第一个字节的时间 |
| CURLINFO_TLS_SESSION | struct curl_slist * | 可用于进一步处理的 TLS 会话信息。（**已弃用选项，请使用 CURLINFO_TLS_SSL_PTR 代替！**） |
| CURLINFO_TLS_SSL_PTR | struct curl_slist * | 可用于进一步处理的 TLS 会话信息 |
| CURLINFO_TOTAL_TIME | double | 上一次传输的总时间 |

# 处理句柄之间共享数据

# 处理句柄之间共享数据

有时应用程序需要在传输之间共享数据。所有添加到同一多句柄的简易句柄在同一多句柄中自动进行了许多共享，但有时这并不是您想要的。

## 多句柄

所有添加到同一多句柄的简易句柄自动共享 cookies、连接缓存、DNS 缓存和 SSL 会话 ID 缓存。

## 在简易句柄之间共享

libcurl 提供了一个通用的“共享接口”，应用程序创建一个“共享对象”，然后该对象保存数据，可以被任意数量的简易处理句柄共享。数据随后存储和读取自共享对象，而不是存储在共享它的处理句柄中。

```
CURLSH *share = curl_share_init(); 
```

共享对象可以设置为共享所有或任何 cookie、连接缓存、DNS 缓存和 SSL 会话 ID 缓存。

例如，设置共享以保存 cookie 和 DNS 缓存：

```
curl_share_setopt(share, CURLSHOPT_SHARE, CURL_LOCK_DATA_COOKIE);
curl_share_setopt(share, CURLSHOPT_SHARE, CURL_LOCK_DATA_DNS); 
```

...然后您设置相应的传输以使用此共享对象：

```
curl_easy_setopt(curl, CURLOPT_SHARE, share); 
```

使用此`curl`句柄完成的传输将使用并存储其 cookie 和 dns 信息在`share`句柄中。您可以设置多个 easy 句柄共享相同的共享对象。

## 分享什么

`CURL_LOCK_DATA_COOKIE` - 设置此位以共享 cookie jar。请注意，每个 easy 句柄仍然需要正确启动其 cookie“引擎”才能开始使用 cookie。

`CURL_LOCK_DATA_DNS` - DNS 缓存是 libcurl 存储已解析主机名地址一段时间以使后续查找更快的地方。

`CURL_LOCK_DATA_SSL_SESSION` - SSL 会话 ID 缓存是 libcurl 存储 SSL 连接的恢复信息，以便能够更快地恢复先前的连接。

`CURL_LOCK_DATA_CONNECT` - 当设置时，此句柄将使用共享连接缓存，因此可能更有可能找到现有连接以重复使用等，这可能会在以串行方式向同一主机执行多个传输时提高性能。

## 锁定

如果您希望在多线程环境中由传输共享对象共享。也许您有一个拥有许多核心的 CPU，并且希望每个核心运行自己的线程并传输数据，但仍希望不同的传输共享数据。那么您需要设置互斥回调。

如果您不使用线程，并且*知道*您以串行一次访问共享对象的方式访问共享对象，则无需设置任何锁。但是，如果有多个传输同时访问共享对象，需要设置互斥回调以防止数据破坏甚至崩溃。

由于 libcurl 本身不知道如何锁定事物，甚至不知道您正在使用什么线程模型，因此您必须确保进行互斥锁定，只允许一次访问。用于 pthread 应用程序的锁回调可能类似于：

```
static void lock_cb(CURL *handle, curl_lock_data data,
                    curl_lock_access access, void *userptr)
{
  pthread_mutex_lock(&lock[data]); /* uses a global lock array */
}
curl_share_setopt(share, CURLSHOPT_LOCKFUNC, lock_cb); 
```

与相应的解锁回调可能如下所示：

```
static void unlock_cb(CURL *handle, curl_lock_data data,
                      void *userptr)
{
  pthread_mutex_unlock(&lock[data]); /* uses a global lock array */
}
curl_share_setopt(share, CURLSHOPT_UNLOCKFUNC, unlock_cb); 
```

## 不共享

待定

# API 兼容性

## API 兼容性

libcurl 承诺 API 稳定性，并保证您今天编写的程序将在未来继续运行。我们不会破坏兼容性。

随着时间的推移，我们向 API 添加功能、新选项和新功能，但我们不以不兼容的方式更改行为或删除功能。

我们上次以不兼容的方式更改 API 是在 2006 年的 7.16.0 版本，我们计划永远不再这样做。

### 版本号

Curl 和 libcurl 具有各自的版本，但它们大多数情况下相互紧密跟随。

版本编号始终使用相同的系统构建：

```
X.Y.Z 
```

+   X 是主版本号

+   Y 是发布号

+   Z 是补丁号

### 提升数字

这些 X.Y.Z 数字中的一个将在每个新版本中被提升。被提升数字右侧的数字将被重置为零。

当进行了*真正*的巨大、影响深远的更改时，主版本号 X 会增加。当进行更改或添加事物/功能时，发布号 Y 会增加。当进行的更改仅是修复错误时，补丁号 Z 会增加。

这意味着在发布 1.2.3 后，如果进行了非常大的更改，我们可以发布 2.0.0，如果没有进行太大的更改，则可以发布 1.3.0，如果主要修复了错误，则可以发布 1.2.4。

增加，即将数字增加 1，无条件地只影响一个数字（其右边的数字设置为零）。1 变成 2，3 变成 4，9 变成 10，88 变成 89，99 变成 100。因此，在 1.2.9 之后是 1.2.10。在 3.99.3 之后，可能是 3.100.0。

所有原始的 curl 源代码发布档案都根据 libcurl 版本命名（而不是根据可能不同的 curl 客户端版本命名）。

### 使用哪个 libcurl 版本

作为对任何可能希望支持新 libcurl 功能的应用程序的一种服务，同时仍然能够使用旧版本进行构建，所有发布版本都将 libcurl 版本存储在 `curl/curlver.h` 文件中，使用静态编号方案可用于比较。版本号定义为：

```
#define LIBCURL_VERSION_NUM 0xXXYYZZ 
```

其中 XX、YY 和 ZZ 分别是十六进制中的主版本号、发布版本号和补丁号。所有三个数字字段始终使用两位数表示（每个八位）。1.2.0 将显示为 "0x010200"，而版本 9.11.7 则显示为 "0x090b07"。

这个 6 位十六进制数在更近期的发布中总是一个更大的数。它使得大于和小于的比较起作用。

此数字也作为三个单独的定义可用：`LIBCURL_VERSION_MAJOR`、`LIBCURL_VERSION_MINOR` 和 `LIBCURL_VERSION_PATCH`。

当然，这些定义仅适用于确定刚刚构建的版本号，它们无法帮助您确定三年后运行时使用的 libcurl 版本。

### 运行的是哪个 libcurl 版本

要确定您的应用程序当前使用的是哪个 libcurl 版本，`curl_version_info()` 就在那里为您服务。

应用程序应该使用此函数来判断是否可以执行某些操作，而不是使用编译时检查，因为动态/DLL 库可以独立于应用程序进行更改。

curl_version_info() 返回一个指向包含有关版本号和正在运行的 libcurl 中各种特性的信息的结构体的指针。调用时，您需要给它一个特殊的年龄计数器，以便 libcurl 知道调用它的 libcurl 的 "年龄"。年龄是一个名为 `CURLVERSION_NOW` 的定义，它是一个在 curl 开发的不规则间隔内不断增加的计数器。年龄数告诉 libcurl 它可以返回哪个结构集。

您可以这样调用该函数：

curl_version_info_data *ver = curl_version_info( CURLVERSION_NOW );

数据将指向具有或至少可以具有以下布局的结构体：

```
struct {
  CURLversion age;          /* see description below */

  /* when 'age' is 0 or higher, the members below also exist: */
  const char *version;      /* human readable string */
  unsigned int version_num; /* numeric representation */
  const char *host;         /* human readable string */
  int features;             /* bitmask, see below */
  char *ssl_version;        /* human readable string */
  long ssl_version_num;     /* not used, always zero */
  const char *libz_version; /* human readable string */
  const char * const *protocols; /* protocols */

  /* when 'age' is 1 or higher, the members below also exist: */
  const char *ares;         /* human readable string */
  int ares_num;             /* number */

  /* when 'age' is 2 or higher, the member below also exists: */
  const char *libidn;       /* human readable string */

  /* when 'age' is 3 or higher (7.16.1 or later), the members below also
     exist  */
  int iconv_ver_num;       /* '_libiconv_version' if iconv support enabled */

  const char *libssh_version; /* human readable string */

} curl_version_info_data; 
```

# --libcurl

## curl --libcurl

我们积极鼓励用户首先尝试使用 curl 命令行工具进行他们想要的传输，一旦它大致按照你想要的方式工作，你就可以在命令行中附加 `--libcurl [filename]` 选项并再次运行它。

`--libcurl` 命令行选项将在提供的文件名中创建一个 C 程序。该 C 程序是一个使用 libcurl 运行刚刚由 curl 命令行工具完成的传输的应用程序。有一些例外情况，它并不总是 100%匹配，但你会发现它可以作为你想要或可以使用的 libcurl 选项以及为它们提供的其他参数的优秀灵感来源。

如果将文件名指定为一个破折号，如 `--libcurl -`，则会将程序写入标准输出而不是文件。

例如，我们运行一个命令来仅获取 [`example.com`](http://example.com)：

```
curl http://example.com --libcurl example.c 
```

这会在当前目录中创建 `example.c`，看起来类似于这样：

```
/********* Sample code generated by the curl command-line tool **********
 * All curl_easy_setopt() options are documented at:
 * https://curl.haxx.se/libcurl/c/curl_easy_setopt.html
 ************************************************************************/
#include <curl/curl.h>

int main(int argc, char *argv[])
{
  CURLcode ret;
  CURL *hnd;

  hnd = curl_easy_init();
  curl_easy_setopt(hnd, CURLOPT_URL, "http://example.com");
  curl_easy_setopt(hnd, CURLOPT_NOPROGRESS, 1L);
  curl_easy_setopt(hnd, CURLOPT_USERAGENT, "curl/7.45.0");
  curl_easy_setopt(hnd, CURLOPT_MAXREDIRS, 50L);
  curl_easy_setopt(hnd, CURLOPT_SSH_KNOWNHOSTS, "/home/daniel/.ssh/known_hosts");
  curl_easy_setopt(hnd, CURLOPT_TCP_KEEPALIVE, 1L);

  /* Here is a list of options the curl code used that cannot get generated
     as source easily. You may select to either not use them or implement
     them yourself.

  CURLOPT_WRITEDATA set to a objectpointer
  CURLOPT_WRITEFUNCTION set to a functionpointer
  CURLOPT_READDATA set to a objectpointer
  CURLOPT_READFUNCTION set to a functionpointer
  CURLOPT_SEEKDATA set to a objectpointer
  CURLOPT_SEEKFUNCTION set to a functionpointer
  CURLOPT_ERRORBUFFER set to a objectpointer
  CURLOPT_STDERR set to a objectpointer
  CURLOPT_HEADERFUNCTION set to a functionpointer
  CURLOPT_HEADERDATA set to a objectpointer

  */

  ret = curl_easy_perform(hnd);

  curl_easy_cleanup(hnd);
  hnd = NULL;

  return (int)ret;
}
/**** End of sample code ****/ 
```

# 头文件

## 头文件

你的 libcurl 使用应用程序只需要包含一个头文件：

```
#include <curl/curl.h> 
```

该文件又包含了一些其他的公共头文件，但你基本上可以假装它们不存在。（从历史的角度来看，我们开始时略有不同，但随着时间的推移，我们稳定下来了，只使用一个头文件进行包含。）

# 全局初始化

## 全局初始化

在程序中进行任何与 libcurl 相关的操作之前，你应该使用 `curl_global_init()` 进行全局 libcurl 初始化调用。这是必要的，因为 libcurl 可能正在使用的一些底层库需要先进行调用来正确设置和初始化。

`curl_global_init()` 不幸地不是线程安全的，所以你必须确保你只调用一次，并且不要与另一个调用同时进行。它初始化全局状态，所以你应该只调用一次，一旦你的程序完全停止使用 libcurl，你可以调用 `curl_global_cleanup()` 来释放和清理初始化调用分配的相关全局资源。

libcurl 构建为处理跳过 `curl_global_init()` 调用的情况，但它会自己调用它（如果你在任何实际文件传输开始之前没有这样做）并使用自己的默认值。但请注意，即使在这种情况下，它仍然不是线程安全的，因此它可能会给你带来一些 "有趣" 的副作用。最好还是以受控的方式自己调用 `curl_global_init()`。

# 多线程

## libcurl 多线程

libcurl 是线程安全的，但没有内部线程同步。你可能需要提供自己的锁定或更改选项以正确使用 libcurl 线程化。具体需要什么取决于 libcurl 的构建方式。请参阅 [libcurl 线程安全](https://curl.haxx.se/libcurl/c/threadsafe.html) 网页，其中包含最新信息。

# curl 简易选项

## 设置句柄选项

您在 easy 句柄中设置选项以控制传输的执行方式，或者在某些情况下，您实际上可以在传输进行时设置选项并修改传输的行为。您使用`curl_easy_setopt()`设置选项，并提供句柄、要设置的选项和选项的参数。所有选项都只接受一个参数，您必须始终向 curl_easy_setopt()调用传递三个参数。

由于 curl_easy_setopt()调用接受几百种不同的选项，而各种选项接受各种不同类型的参数，因此非常重要阅读具体内容，并提供特定选项支持和期望的确切参数类型。传递错误类型可能导致意外副作用或难以理解的问题。

每个传输可能最重要的选项是 URL。libcurl 无法在不知道涉及哪个 URL 的情况下执行传输，因此您必须告诉它。URL 选项名称为`CURLOPT_URL`，因为所有选项都以`CURLOPT_`为前缀，然后是描述性名称——全部使用大写字母。设置将 URL 设置为获取"[`example.com`](http://example.com)" HTTP 内容的示例行可能如下：

```
CURLcode ret = curl_easy_setopt(easy, CURLOPT_URL, "http://example.com"); 
```

再次强调：这只是在句柄中设置选项。它不会执行实际传输或其他任何操作。它基本上只是告诉 libcurl 复制字符串，如果成功则返回 OK。

当然，检查返回代码以确保没有出现问题是一个好习惯。

### 设置数字选项

由于 curl_easy_setopt()是一个可变参数函数，第三个参数可以根据情况使用不同类型，因此无法进行正常的 C 语言类型转换。因此，**必须**确保您确实传递了'long'而不是'int'，如果文档告诉您如此。在它们大小相同的架构上，您可能不会遇到任何问题，但并非所有都是这样。同样，对于接受'curl_off_t'类型的选项，**至关重要**的是您传递使用该类型而不是其他类型的参数。

强制为 long：

```
curl_easy_setopt(handle, CURLOPT_TIMEOUT, 5L); /* 5 seconds timeout */ 
```

强制为 curl_off_t:

```
curl_off_t no_larger_than = 0x50000;
curl_easy_setopt(handle, CURLOPT_MAXFILE_LARGE, no_larger_than); 
```

### 获取句柄选项

不，没有通用方法可以提取之前使用`curl_easy_setopt()`设置的相同信息！如果您需要能够再次提取您之前设置的信息，那么我们鼓励您在应用程序中自行跟踪这些数据。

# CURLcode 返回代码

## CURLcode 返回代码

许多 libcurl 函数返回一个 CURLcode。这是一个特殊的 libcurl typedefed 变量，用于错误代码。如果一切正常，它将返回`CURLE_OK`（其值为零），如果检测到问题，则返回非零数字。几乎有一百个`CURLcode`错误在使用中，您可以在`curl/curl.h`头文件中找到它们，并在 libcurl-errors 手册页中找到它们的文档。

您可以使用 `curl_easy_strerror()` 函数将 CURLcode 转换为人类可读的字符串，但请注意，这些错误很少以适合在 UI 中向任何人公开或向最终用户公开的方式表达：

```
const char *str = curl_easy_strerror( error );
printf("libcurl said %s\n", str); 
```

在发生错误时，另一种获取稍微更好的错误文本的方法是将 `CURLOPT_ERRORBUFFER` 选项设置为指向程序中的缓冲区，然后 libcurl 将在返回错误之前在那里存储相关的错误消息：

```
curl error[CURL_ERROR_SIZE]; /* needs to be at least this big */
CURLcode ret = curl_easy_setopt(handle, CURLOPT_ERRORBUFFER, error); 
```

# 冗长的操作

## 冗长的操作

好吧，我们刚刚展示了如何将错误作为人类可读的文本获取，因为这对于弄清楚特定传输出了什么问题并经常解释为什么可以这样做或者问题出在哪里非常有帮助。

写 libcurl 应用程序时的下一个救星，每个人都需要了解并且至少在开发 libcurl 应用程序或调试 libcurl 本身时需要广泛使用，那就是使用 `CURLOPT_VERBOSE` 启用 "详细模式"：

```
CURLcode ret = curl_easy_setopt(handle, CURLOPT_VERBOSE, 1L); 
```

当告诉 libcurl 要冗长时，它将在传输正在进行时将与传输相关的详细信息和信息输出到 stderr。这对于弄清楚为什么事情失败以及在您询问它不同的事情时 libcurl 到底做了什么非常有用。您可以通过更改 stderr 为 `CURLOPT_STDERR` 重定向输出，或者您可以通过调试回调以更精致的方式获取更多信息（在后面的一节中进一步解释）。

### 追踪所有事物

冗长是完全可以的，但有时您需要更多。libcurl 还提供了一个跟踪回调，除了显示详细模式所显示的所有内容之外，还传递了*所有*发送和接收的数据，以便您的应用程序获得关于所有内容的完整跟踪。

传递给跟踪回调的发送和接收数据以其未加密的形式传递给回调函数，这在处理基于 TLS 或 SSH 的协议时非常方便，因为在网络上捕获数据以进行调试并不是很实用。

当您设置了 `CURLOPT_DEBUGFUNCTION` 选项时，仍然需要启用 `CURLOPT_VERBOSE`，但是通过设置跟踪回调 libcurl 将使用该回调而不是其内部处理。

跟踪回调应该匹配以下原型：

```
int my_trace(CURL *handle, curl_infotype type, char *ptr, size_t size,
             void *userp); 
```

**handle** 是易于处理的句柄，**type** 描述了传递给回调函数的特定数据（数据输入/输出、头部输入/输出、TLS 数据输入/输出和 "text"），**ptr** 指向的数据是 **size** 字节的数据。**userp** 是您用 `CURLOPT_DEBUGDATA` 设置的自定义指针。

**ptr** 指向的数据*不会*以零终止，但其大小将完全由 **size** 参数指定。

回调函数必须返回 0，否则 libcurl 将视为错误并中止传输。

在 curl 网站上，我们托管了一个名为 [debug.c](https://curl.haxx.se/libcurl/c/debug.html) 的示例，其中包含一个简单的跟踪函数以供参考。

在 [CURLOPT_DEBUGFUNCTION man page](https://curl.haxx.se/libcurl/c/CURLOPT_DEBUGFUNCTION.html) 中还有更多细节。

# libcurl 示例

# libcurl 示例

libcurl 的本机 API 是用 C 编写的，因此本章重点介绍用 C 编写的示例。但由于 libcurl 的许多语言绑定都很简单，它们通常公开的函数多多少少相同，因此它们对其他语言的用户也可能是有趣且教育性的。

## 获取简单的 HTML 页面

此示例仅获取 HTML 并将其发送到 stdout：

```
#include <stdio.h>
#include <curl/curl.h>

int main(void)
{
  CURL *curl;
  CURLcode res;

  curl = curl_easy_init();
  if(curl) {
    curl_easy_setopt(curl, CURLOPT_URL, "http://example.com/");

    /* Perform the request, res will get the return code */
    res = curl_easy_perform(curl);
    /* Check for errors */
    if(res != CURLE_OK)
      fprintf(stderr, "curl_easy_perform() failed: %s\n",
              curl_easy_strerror(res));

    /* always cleanup */
    curl_easy_cleanup(curl);
  }
  return 0;
} 
```

## 在内存中获取 HTML 页面

此示例是前一个示例的变体，不是将数据发送到 stdout（通常不是你想要的），而是将接收到的数据存储在内存缓冲区中，随着传入数据的增长而变大。

通过使用写回调来接收数据来实现此目的。

```
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <curl/curl.h>

struct MemoryStruct {
  char *memory;
  size_t size;
};

static size_t
WriteMemoryCallback(void *contents, size_t size, size_t nmemb, void *userp)
{
  size_t realsize = size * nmemb;
  struct MemoryStruct *mem = (struct MemoryStruct *)userp;

  mem->memory = realloc(mem->memory, mem->size + realsize + 1);
  if(mem->memory == NULL) {
    /* out of memory! */
    printf("not enough memory (realloc returned NULL)\n");
    return 0;
  }

  memcpy(&(mem->memory[mem->size]), contents, realsize);
  mem->size += realsize;
  mem->memory[mem->size] = 0;

  return realsize;
}

int main(void)
{
  CURL *curl_handle;
  CURLcode res;

  struct MemoryStruct chunk;

  chunk.memory = malloc(1);  /* will be grown as needed by the realloc above */
  chunk.size = 0;    /* no data at this point */

  curl_global_init(CURL_GLOBAL_ALL);

  /* init the curl session */
  curl_handle = curl_easy_init();

  /* specify URL to get */
  curl_easy_setopt(curl_handle, CURLOPT_URL, "http://www.example.com/");

  /* send all data to this function  */
  curl_easy_setopt(curl_handle, CURLOPT_WRITEFUNCTION, WriteMemoryCallback);

  /* we pass our 'chunk' struct to the callback function */
  curl_easy_setopt(curl_handle, CURLOPT_WRITEDATA, (void *)&chunk);

  /* some servers don't like requests that are made without a user-agent
     field, so we provide one */
  curl_easy_setopt(curl_handle, CURLOPT_USERAGENT, "libcurl-agent/1.0");

  /* get it! */
  res = curl_easy_perform(curl_handle);

  /* check for errors */
  if(res != CURLE_OK) {
    fprintf(stderr, "curl_easy_perform() failed: %s\n",
            curl_easy_strerror(res));
  }
  else {
    /*
     * Now, our chunk.memory points to a memory block that is chunk.size
     * bytes big and contains the remote file.
     *
     * Do something nice with it!
     */

    printf("%lu bytes retrieved\n", (long)chunk.size);
  }

  /* cleanup curl stuff */
  curl_easy_cleanup(curl_handle);

  free(chunk.memory);

  /* we're done with libcurl, so clean it up */
  curl_global_cleanup();

  return 0;
} 
```

## 通过 HTTP 提交登录表单

待定

## 获取 FTP 目录列表

待定

## 直接将 HTTPS 页面下载到内存中

待定

## 在不阻塞的情况下将数据上传到 HTTP 站点

待定

# 适用于 C++ 程序员

# 适用于 C++ 程序员的 libcurl

待定

+   字符串是 C 字符串，而不是 C++ 字符串对象

+   回调考虑事项
