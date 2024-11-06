# 什么是 RPC？

## 什么是 RPC？

#### RPC（Remote Procedure CallProtocol）——远程过程调用协议，它是一种通过网络从远程计算机程序上请求服务，而不需要了解底层网络技术的协议。

#### 简单来说 rpc 就是 client 在不知道任何底层实现的情况下，可以直接调用 server 的函数方法；而 server 也可以直接调用 client 的函数。

#### 百度给出的流程图：

## ![](img/18d8bc3eb13533fadd93e964a9d3fd1f41345b56.jpg)

#### 简单了解了什么是 rpc，下面我就来在我们的 server 和 client 来实现 rpc 的功能。

# 我的服务器上的 RPC

## 我的服务器上的 RPC

##### 下面是之前我们给出的 tcpserver 中的一个函数，用来处理连接

```
def _handle_connect(self, sock):
    conn = self._build_class(sock, **self._build_kwargs)
    self.on_connect(conn)

    close_callback = functools.partial(self.on_close, conn)
    conn.set_close_callback(close_callback) 
```

##### build_class 之前我们说过，这是我们用来处理数据的 protocol，那么 rpc 的逻辑流程应该都写在这里。现在假设 client 来调用一个函数 sum(x, y)， 那么在我们 server 中就要有这样一个函数。

```
def sum(x, y):
    return x+y 
```

但是客户端来调用，我们如何知道 server 有这样一个函数呢？这就需要我们提前去处理一下，将希望可以被 client 调用的函数存起来。

```
def route(**options):
    def decorator(handler):
        msgid = options.pop('msgid', handler.__name__)
        elif not msgid in HANDLERS:
            HANDLERS[msgid] = handler
        else:
            raise Exception('[ ERROR ]Handler "%s" exists already!!' % msgid)
        return handler
    return decorator 
```

比如我们可以写这样一个函数，作为装饰器，来将被装饰的函数存起来(HANDLERS)，这样在 client 调用 sum 的时候，我们就可以知道，server 中是否存在 sum 这个函数。

```
@route()
def sum(x, y):
    return x+y 
```

这样函数被装饰起来以后，我们就可以找到这个函数了。当我们知道存在 sum 这个函数的时候，我就可以从 HANDLERS 中取出 sum，`sum = HANDLERS.get('sum')`，然后我们将 x，y 两个参数传进去，算出结果，再将结果写回 conn 中，返回给 client。至此，客户端调用服务器函数的大致流程就说完了。

# 我的客户端上的 RPC

## 我的客户端上的 RPC

##### 服务器调用 client 函数也是一样的道理，client 中也要和服务器一样，将想要被调用的函数收集起来。当然这个时候，��务器还要做一件事情，就是将客户端的 tcp 连接通过某种条件储存起来，这样才知道我想去调用哪个 client 的函数。

##### 现在有很多 client 来连接我们 server，以游戏为例，每个玩家都有自己对应的 uid，那么我们就可以将 conn 根据 uid 储存起来。`client_conn = {uid:conn, ..}` 这样，我们想给哪位玩家发送消息或者做一些其他的事情，就很容易了，只要客户端写好函数功能，我们只要将函数名字，以及对应参数，通过 client_conn 找到对应玩家的 tcp 连接，然后将上述数据发送过，那么当客户端计算出结果以后，我们通过一个回调函数，就可以将结果 return 到服务器了。

现有的 rpc 框架很多，比如[msgpack-python](https://github.com/msgpack-rpc/msgpack-rpc-python)，这里有很多语言的 rpcSimpleServer，感兴趣的同学可以参考一下。
