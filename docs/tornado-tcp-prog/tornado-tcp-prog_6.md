# 让我们实战吧

#### 本章主要介绍一些开发中的小例子，小问题，小技巧。

# 正确关闭服务器的姿势

### 1.正确关闭服务器的姿势

##### 有时候，服务器的进程因为某种原因被关闭或者自己手动关闭，无法保证内存里的数据正确入库或者仍有 cb 函数没有执行，这个时候，我们就要确保一切都正确的被执行完毕后，再关闭服务器。

```
def sig_handler(sig, frame):
    logger.warning('Caught signal: %s', sig)
    ioloop.IOLoop.instance().add_callback(shutdown)

def shutdown():
    io_loop = ioloop.IOLoop.instance()
    server.stopFactory() ##自己去做一些处理，保证入库等。

    deadline = time.time() + 5

    def stop_loop():
        now = time.time()
        if now < deadline and io_loop._callbacks:
            io_loop.add_timeout(now + 1, stop_loop)
        else:
            io_loop.stop() # 处理完现有的 callback 后，结束 ioloop 循环
    stop_loop()

def start():
    log_initialize()
    global server
    server = RPCServer(('localhost', 5700))
    server.start()

    signal.signal(signal.SIGTERM, sig_handler)
    signal.signal(signal.SIGINT, sig_handler) 
```

# 自动收集 rpc 函数

### 2.自动收集 rpc 函数

##### 服务器可被客户端调用的函数，不会有多少就去写多少到字典中, 所以需要自动去收集可被调用函数,这样就方便许多。

```
collect.py

#1.第一种方法也比较傻，适合 rpc 文件较少的情况
import rpc1

DICT = {}

for name in dir(rpc1):
    if name.startswith("__") or name.endswith("__"):
        continue
    DICT[name] = getattr(rpc1, name)

rpc1.py

#被调用函数
def func():
    return 1 
```

```
#第二种相对智能一些
将所有可被调用函数的文件写入固定文件夹中，比如取名为 handler 的文件夹。直接将模块 import 或者也可以写入一个字典中
#name 为当前文件与 handler 的相对路径
_imported = []
for f in os.listdir(name + "/handler"):
    if f.find('.pyc') > 0:
        _subfix = '.pyc'
    elif f.find('.pyo') > 0:
        _subfix = '.pyo'
    elif f.find('.py') > 0:
        _subfix = '.py'
    else:
        continue

    fname, _ = f.rsplit(_subfix, 1)
    if fname and fname not in _imported:
        _handlers_name = '%s.%s' % (module, fname)
        __import__(_handlers_name)
        _imported.append(fname) 
```

# 和数据库的那些事

### 3.和数据库的那些事

##### 在开发中,数据库是必不可少的, 因此这节主要来说一下常用的两种类型数据库,mysql 和 redis 的简单使用

```
#1.mysql 算是最常用的数据库之一了,不要钱,功能齐全,性能优良。这里主要使用 tornado 的一款 api,
#tornado_mysql。

from tornado_mysql      import pools
from tornado            import gen
from tornado            import ioloop
from tornado.concurrent import Future
from pool               import threadpool

import functools

SYNC, ROW, DATASET = range(3)

__pool = None

ioloop = ioloop.IOLoop.current()

def init(**conf):
    global __pool

    if not __pool:
        __pool = pools.Pool(conf, max_idle_connections=5, max_recycle_sec=3)

@gen.coroutine
def execute(sql, value=None, operator=SYNC):
    assert __pool is not None

    result = None
    if value is None:
        cur = yield __pool.execute(sql)
    else:
        yield __pool.execute(sql, value)
    if operator == ROW:
        result = cur.fetchone()
    elif operator == DATASET:
        result = cur.fetchall()
    raise gen.Return(result)

fetchone = functools.partial(execute, operator=ROW)
fetchall = functools.partial(execute, operator=DATASET)
#对几种简单的数据库操作进行了简单的封装,便于开发中的使用。 
```

```
#2.redis 算是比较常用的数据库之一，一般使用来做 cache,也有做消息队列的。这里用的是
#tornadoredis 这款 api。

import tornadoredis
from tornado import gen
from tornado.concurrent import Future

pool = None

def init():
    global pool

    if not pool:
        CONNECTION_POOL = tornadoredis.ConnectionPool(max_connections=500, wait_for_available=True)
        pool = tornadoredis.Client(connection_pool=CONNECTION_POOL, selected_db=12) 

@gen.coroutine
def close():
    if pool:
        yield pool.disconnect()

@gen.coroutine
def batch(commands):
    assert pool is not None
    result = None
    try:
        pipe = pool.pipeline()

        for _cmd in commands:
            _op   = _cmd[0]
            _args = _cmd[1]

            if len(_cmd) > 2:
                _kwargs = _cmd[2]
            else:
                _kwargs = {}

            getattr(pipe, _op)(*args, **kwargs)

        result = yield gen.Task(pipe.execute)
    except Exception as e:
        print e

    raise Return(result)

def execute(cmd, *args, **kwargs):
    assert pool is not None
    f = Future()
    def onResult(result):
        f.set_result(result)

    result = None
    _func  = getattr(pool, cmd)
    _func(callback=onResult, *args, **kwargs)
    return f

#对 redis 的操作进行了统一封装,直接使用 execute 就可以, 将命令作为参数传递。多个命令的执行可以使用 batch 来执行, 使用 pipe 提高执行效率。 
```

# 跟多线程搞一些事情

### 跟多线程搞一些事情

至今我仍然坚信，单线程仍然是最有效率的方式，比如 nginx 就是个很好的例子，在 python 中尤其。但是 tornado 依然提供了多线程方式来给开发者。这里给出一个例子，并做出简单的解释。

```
EXECUTOR = ThreadPoolExecutor(max_workers=4)＃最大线程数

def unblock(f):
    @tornado.web.asynchronous
    @wraps(f)
    def wrapper(*args, **kwargs):
        self = args[0]
        def callback(future):
            self.write(future.result())#将 f 结果写回给 client
            self.finish()

        EXECUTOR.submit(
                partial(f, *args, **kwargs)#启用多线程
                ).add_done_callback(#因为是异步执行，所以返回值是 future
                        lambda future: tornado.ioloop.IOLoop.instance().add_callback(
                            partial(callback, future)))#最后写回 client 的步骤要在主线程中完成，否则会出错，因此需要通过回调来将 f 返回的 future 返回到主线程中。
    return wrapper

class MainHandler(tornado.web.RequestHandler):
    @unblock
    def get(self):
        sleep(3)
        #self.write("ff")
        return "ff" 
```

线程库用的是 futures 里提供的，比较简单，没有安装的童鞋，可以用 pip install futures 来进行安装. 上面的例子用的是最简单的 http 请求，tcp 中也是同样一个道理，只需要讲 self.write 和 finish 替换成自己写 socket 的函数就可以了。

另外由于 GIL 的限制，多线程并不能达到利用多核的目的，因此还是要使用传统的多进程来实现，或者也可以使用比较流行的协程提高效率。最理想的情况就是 netty 那样的模型，但是因为 python 线程的问题，因此可以将线程替换为 stackless 中的微进程，每一条连接分配一个 stackless，这样也可以达到一个目的。现成的有人将 stackless 与 twisted 在一起使用，具体效果没有测试过。

# tornado 和 celery 很配呦

### tornado 和 celery 很配呦

Celery 是一个简单、灵活且可靠的，处理大量消息的分布式系统，并且提供维护这样一个系统的必需工具。它是一个专注于实时处理的任务队列，同时也支持任务调度。在我们日常的开发中，或多或少都会用到，一些比较耗时的异步任务，一些定时的任务都可以用 celery 去做。

在 tornado 中如果想使用 celery，首先要安装 celery 的 python api。使用 pip install celery 就可以了，非常方便。

```
from celery import Celery, task

c = Celery()

这是最基本的用法。

我们想要定义一个任务，我们就可以写一个很普通的方法，比如

@task
def mytask(a):
    print 1111

只要加上@task 这样一个装饰器，它就会标识为一个 celery 的 task。我们就可以调用他了。

首先我们要启动 celery，下面是我的启动命令
celery -A my.utils.async_task worker -P gevent -c 2 -l info -n 'my.worker.%%h.%(ENV_USER)s'

相关参数官方文档中都可以查到，这里就不一一详述了。

调用的时候，我们要这样

v = mytask.apply_async(111, countdown=1)
他的返回值是他的任务 id，通过任务 id，我们可以取消任务,countdown 代表多少秒以后执行

revoke 函数就是取消任务的，revoke(task_id) 
```

# 监控你的 api

# 监控你的 api

influxdb grafana
