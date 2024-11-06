# ioloop

# 2.ioloop

说到 tornado，那就不得不说他的 ioloop，这是这个框架的灵魂所在。通过一段简单的代码，来开启 tornado tcp 编程的大门。

```
import errno
import functools
import tornado.ioloop
import socket

def connection_ready(sock, fd, events):
    while True:
        try:
            connection, address = sock.accept()
        except socket.error as e:
            if e.args[0] not in (errno.EWOULDBLOCK, errno.EAGAIN):
                raise
            return
        connection.setblocking(0)
        handle_connection(connection, address)

if __name__ == '__main__':
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    sock.setblocking(0)
    sock.bind(("", port))
    sock.listen(128)

    io_loop = tornado.ioloop.IOLoop.current()
    callback = functools.partial(connection_ready, sock)
    io_loop.add_handler(sock.fileno(), callback, io_loop.READ)
    io_loop.start() 
```

这是官方文档给出的一段简单的 tcpserver 的代码，那么我们就从它来分析一下。 首先是 socket 的部分，创建了一个 socket，然后下面是 ioloop 的部分。首先我们创建一个 ioloop 实例, 然后创建了一个回调函数, （partial 这个函数不用太关心，就是一种绑定参数的函数写法。）然后给 ioloop 加上一个 handler，用于监听 socket，最后开启 ioloop。当 ioloop 开启以后，就会去执行回调函数 connecction_ready。

以上就是创建一个 simpleTCPServer 的步骤，接下来我们主要围绕 ioloop 来说一下与它相关的函数方法。

# ioloop 的基本函数

## 2.1 ioloop 的基本函数

##### 1.IOLoop.current(instance=True)

如果当前的 ioloop 已经运行了，那么这个函数就是用来获得当前线程里的 IOLoop 对象。

##### 2.IOLoop.start()

这个函数就很简单了，就是开启我们的 ioloop，它会一直运行下去，直到有人调用了 stop()。

##### 3.IOLoop.stop()

这个就是上面说的用来停止 ioloop 循环的。

##### 4.IOLoop.run_sync(func, timeout=None)

这个函数是在 ioloop 开启时去执行 func 这个函数，然后关闭 ioloop，func 执行完它会自动执行 stop()，这个不用担心。

```
@gen.coroutine
def main():
    # do sth...

if __name__ == '__main__':
    IOLoop.current().run_sync(main) 
```

##### 5.add_handler(fd, handler, events)

注册一个 handler，从 fd 那里接受事件。 fd 呢就是一个描述符，events 就是要监听的事件。 events 有这样几种类型，IOLoop.READ, IOLoop.WRITE, 还有 IOLoop.ERROR. 很好理解，读写事件，还有错误异常。

当我们选定的类型事件发生的时候，那么就会执行 handler(fd, events)。

##### 6.update_handler(fd, events)

用来更新上面我们注册的 handler 的。

##### 7.remove_handler(fd)

停止监听 fd 上面的所有事件。

以上就是在 ioloop 开启的时候，涉及到的主要函数及其作用的介绍。

# ioloop 的回调函数

## 2.2 ioloop 的回调函数

##### 1.IOLoop.add_callback(callback, *args, **kwargs)

这个函数是最简单的，在 ioloop 开启后执行的回调函数 callback，*args 和**kwargs 都是这个回调函数的参数。一般我们的 server 都是单进程单线程的，即使是多线程，那么这个函数也是安全的。

##### 2.IOLoop.add_callback_from_signal(callback, *args, **kwargs)

这个函数和上面的很类似，只不过他是在 without any stack_context 的时候去执行，关于 stack_context，查阅[这里](http://www.tornadoweb.org/en/stable/stack_context.html#module-tornado.stack_context)。

##### 3.IOLoop.add_future(future, callback)

这个函数呢也是添加一个 callback 函数，当给定的这个 future 执行完的时候，callback 会去执行，这个函数有唯一的一个参数就是这个 future 对象。关于 future 呢，后面会详细去讲。

##### 4.IOLoop.add_timeout(deadline, callback, *args, **kwargs)

执行 callback 函数在 deadline 的时候，这个 deadline 可以是 time.time，也可以是 datetime.timedelta。还有，这个函数线程不安全。

##### 5.IOLoop.call_at(when, callback, *args, **kwargs)

这个函数我们用的就很多了，在 ioloop 启动后，会在 when 这个时间点去执行 callback 函数。类似一个定时器的功能。

##### 6.IOLoop.call_later(delay, callback, *args, **kwargs)

这个函数和上面的差不多，这是在 ioloop 启动后的 delay 秒后，去执行 callback。上面的是一个时间点，而这个函数是多少秒。 `ioloop.IOLoop.current().call_later(3, func)`这就是在 ioloop 启动的 3s 以后来执行 func 函数。

##### 7.IOLoop.remove_timeout(timeout)

这个函数就是用来移除上面通过 add_timeout 注册的 callback 函数。

##### 8.IOLoop.spawn_callback(callback, *args, **kwargs)

这个函数也是去执行一个回调函数，但是和上面说过的其他 callback 不同，它和回调者的栈上下文没有关联，因此呢，他比较时候去做一些独立的功能回调。

##### 9.IOLoop.time()

它返回的时候 ioloop 开启后的时间，返回的值跟 time.time 差不多。

# ioloop 相关函数说明

## 2.3 ioloop 相关函数说明

1.add_handler, update_handler, remove_handler 三个和 handelr 有关的函数，通常是在写 connection 的时候用到的，刚开始学习的时候，不用太在意它的用法，在后面会详细说明。

2.add_callback 是比较常用的函数之一，不管在 tornado 还是其他的异步框架中，回调都是非常常见的。在服务器启动以后，会有一些相关的操作需要在 ioloop 启动后才能有效的去执行，那么这个时候，添加一个 callback 就是非常必要的了。以游戏服务器为例子(可能不贴切)，在游戏服务器启动后，会把全服的排行榜数据 load 到内存中，那么这个时候就可以使用 add_callback 了。

```
io_loop = ioloop.IOLoop.instance()
io_loop.add_callback(load_rank_list)
io_loop.start() 
```

其中 load_rank_list 就是去将排行榜信息 load 到内存中的相关操作。

3.call_later 和 call_at 也是我们在开发过程中常用的函数之一。它们给我们在做相关定时的操作的时候带来了便利。举个简单的例子，在晚上 9 点需要向玩家发放一些奖励道具，那么我就可以用到 call_at

`call_at(time, func, *args, **kw)`

time 就是晚上 9 点的时间戳，func 就是发放奖励的函数，后面是相关参数。call_later 同理，在第一次发完以后，我们就可以使用 call_later()来进行一个循环的操作， `call_later(86400, func)` 这样每过 86400s(一天)，就可以再次发放奖励。

4.ioloop 的完全开启，也就相当于我们整个服务器开启，如果想要获得服务器从开启到现在的过了多久，那么 IOLoop.time()就可以帮助我们得到它。
