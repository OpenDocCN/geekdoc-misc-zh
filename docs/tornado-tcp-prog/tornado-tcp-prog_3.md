# what' the iostream?

# 3.what's the iostream

我们了解了关于 ioloop 的一些相关函数，我想现在对 tornado 的一些功能也有了大概的了解。这一章我们简单的了解一下 tornado 里的 iostream。我们写一个服务器，所有的 io 都要通过一个 connection 来传输，那么 iostream 里就包含了我们对数据的处理，以及对连接的一些操作。

本章主要对 BaseIOStream 和 IOStream 这两个类来进行讲解。官方文档见[这里](http://www.tornadoweb.org/en/stable/iostream.html)。

# BaseIOStream 的相关接口

## 3.1BaseIOStream 的相关接口

简单的来说，这个类从 socket 中读或写数据。

以下是它的几个基本属性：

```
io_loop – 当前的 ioloop 实例。
max_buffer_size – 最大的可接受数据大小，默认是 100M。
read_chunk_size – 读取的数据大小，默认 64k。
max_write_buffer_size – 最大的写 buffer 大小。 
```

这些都可以在继承的时候修改的。

介绍一下主要的几个接口

##### 1.BaseIOStream.write(data, callback=None)

异步的写数据，如果有 callback，那么在所有数据成功写入以后执行 callback。

##### 2.BaseIOStream.read_bytes(num_bytes, callback=None, streaming_callback=None, partial=False)

异步的读取数据，读到的数据大小取决于 num_bytes。同理，如果有 callback，在数据完全读取后，执行 callback。读取到的数据 data 作为 callback 的参数，如果不是的话，那么 callback 需要返���一个 future 对象。��streaming_callback,是当读取到的数据全都是有效的情况下，才会去执行。

##### 3.BaseIOStream.read_until(delimiter, callback=None, max_bytes=None)

同上，只不过是当读 delimiter(分隔符)的时候停止。callback 和 read_bytes 里的一样。

##### 4.BaseIOStream.read_until_regex(regex, callback=None, max_bytes=None)

通过正则来读取数据，regex 就是给定的正则表达式。

##### 5.BaseIOStream.read_until_close(callback=None, streaming_callback=None)

异步读数据，知道 socket 关闭。

##### 6.BaseIOStream.close(exc_info=False)

关闭当前的 stream。

##### 7.BaseIOStream.set_close_callback(callback)

当 stream 关闭时，执行回调函数。

##### 8.BaseIOStream.closed()

如果为真，那么说明 stream 已经关闭了。

##### 9.BaseIOStream.reading()

如果为真，那么说明当前正在从 stream 中读数据

##### 10.BaseIOStream.writing()

有读就有写。

以上呢就是 baseIOStream 中，主要的接口。在我们自己去写 connection 的时候，都会用的到，这里先简单介绍一下，在后面写 connection 的时候，我们会着重去讲解。

# baseIOStream 的相关函数以及 IOStream 类

## 3.2 baseIOStream 的相关函数以及 IOStream 类

###### 1.BaseIOStream.fileno()

这个很简单，就是我们 stream 当前的文件描述符。

##### 2.BaseIOStream.close_fd()

关闭这个 fd。

##### 3.BaseIOStream.write_to_fd(data)

尝试向这个 fd 去写 data， 期间可能会出现未成功写入，因此函数的返回值是成功写入数据的大小。

##### 4.BaseIOStream.read_from_fd(data)

有写也有读。

##### 5.BaseIOStream.get_fd_error()

获取 fd 中所有 error 信息。

关于 baseIOStream 的信息差不都就这些了，在我们实际使用的过程中，我们不会去直接使用这个类的，我们基本都会去使用它的子类，IOStream。

以下通过官方文档的例子，来简单介绍一下 IOStream。

```
import tornado.ioloop
import tornado.iostream
import socket

def send_request():
    #向目标写数据
    stream.write(b"GET / HTTP/1.0\r\nHost: friendfeed.com\r\n\r\n")
    #读数据，执行回调 on_headers
    stream.read_until(b"\r\n\r\n", on_headers)

def on_headers(data):
    headers = {}
    for line in data.split(b"\r\n"):
       parts = line.split(b":")
       if len(parts) == 2:
           headers[parts[0].strip()] = parts[1].strip()
    #读数据，最后关闭 stream，ioloop
    stream.read_bytes(int(headers[b"Content-Length"]), on_body)

def on_body(data):
    print(data)
    stream.close()
    tornado.ioloop.IOLoop.current().stop()

if __name__ == '__main__':
    #创建一个 socket
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    #创建一个 stream
    stream = tornado.iostream.IOStream(s)
    #连接目标，执行回调函数 send_request
    stream.connect(("friendfeed.com", 80), send_request)
    开启 ioloop
    tornado.ioloop.IOLoop.current().start() 
```

# Tcp Client 和 Tcp Server

## 3.3 Tcp Client 和 Tcp Server

#### tornado.tcpclient.TCPClient(resolver=None, io_loop=None)

这个呢就是 tornado 自有的一个 tcpclient，使用它的时候，可以直接继承它.

它有一个方法 `connect(host, port, af=<AddressFamily.AF_UNSPEC: 0>, ssl_options=None, max_buffer_size=None)`

它会返回 IOStream 的实例，如果 ssl_options 为真，那么会返回 SSLIOStream。

通过给的 host 和 port 来连接服务器，然后通过返回的 stream，就可以进行读写等操作了。

#### tornado.tcpserver.TCPServer(io_loop=None, ssl_options=None, max_buffer_size=None, read_chunk_size=None)

这个就是用来创建 TCPserver 的。它是非阻塞，单线程的。

来看一下关于它的几个函数

##### 1.listen(port, address="")

```
server = TCPServer()
server.listen(8888)
IOLoop.current().start() 
```

这就可以创建一个简单的 tcpserver，端口号 8888

##### 2.bind(port, address=None, family=<addressfamily.af_unspecu0003a u00030="" class="calibre16">, backlog=128)</addressfamily.af_unspecu0003a>

开启多进程的一个方法

```
server = TCPServer()
server.bind(8888)
server.start(0)  # Forks multiple sub-processes
IOLoop.current().start() 
```

##### 3.add_sockets(sockets)

也可以开启多进程。

```
sockets = bind_sockets(8888)
tornado.process.fork_processes(0)
server = TCPServer()
server.add_sockets(sockets)
IOLoop.current().start() 
```

##### 4.handle_stream(stream, address)

这是我们用来接收 stream 的方法。你可以通过继承 TCPServer，来覆盖这个方法。

几个方法非常简单，都是最基本的，在写 server 的时候都需要用到的。下一节我们来写一个简单的 tcpserver。

# 一个简单的 TCPServer

## 3.4 一个简单的 TCPServer

以下是一个简单的 TCPServer 的代码(鸣谢 yoki123)。

```
class TcpServer(object):
    def __init__(self, address, build_class, **build_kwargs):
        self._address = address
        self._build_class = build_class
        self._build_kwargs = build_kwargs

    def _accept_handler(self, sock, fd, events):
        while True:
            try:
                获得 conn
                connection, address = sock.accept()
            except socket.error, e:
                return

            #通过 conn 解析
            self._handle_connect(connection)

    def _handle_connect(self, sock):
        #这里的 conn 主要是我们来解析数据的 protocol
        conn = self._build_class(sock, **self._build_kwargs)
        self.on_connect(conn)

        close_callback = functools.partial(self.on_close, conn)
        #设置一个 conn 关闭时执行的回调函数
        conn.set_close_callback(close_callback)

    def startFactory(self):
        pass

    def start(self, backlog=0):
        #创建 socket
        socks = build_listener(self._address, backlog=backlog)

        io_loop = ioloop.IOLoop.instance()
        for sock in socks:
            #接受数据的 handler
            callback = functools.partial(self._accept_handler, sock)
            #为 ioloop 添加 handler，callback
            io_loop.add_handler(sock.fileno(), callback, WRITE_EVENT | READ_EVENT | ERROR_EVENT)
        #在 ioloop 开启后，添加一个回调函数
        ioloop.IOLoop.current().add_callback(self.startFactory)

    #接受 buff 的函数，继承 tcpserver 的时候可以重写。
    def handle_stream(self, conn, buff):
        logger.debug('handle_stream')

    def stopFactory(self):
        pass

    def on_close(self, conn):
        logger.debug('on_close')

    def on_connect(self, conn):

        logger.debug('on_connect: %s' % repr(conn.getaddress()))

        handle_receive = functools.partial(self.handle_stream, conn)
        conn.read_util_close(handle_receive) 
```

我们来看一下流程，

##### 1.start().我们开启 tcpserver，首先创建一个 socket，, 然后我们为 ioloop 添加 handler。

##### 2.服务器开启后，执行 _accept_handler,这个函数里是一个循环，从 socket 中获取 conn

##### 3.然后我们解析这个 conn， build_class 使我们自己实现的一个用来解析数据，拆包解包的一个 protocol 类，这里我们会将所有的 bytes 解析为我们能看懂的字符串数字等���。

##### 4.然后我们调用 on_connect 函数，我们将这个 conn 传入 handler_stream 中， 前面讲过，这个函数是用来接受的 stream 的。然后我们从 stream 中读取数据，直到 conn 关闭。

以上就是我们服务器开启后执行的大概流程。
