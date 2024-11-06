# 安装软件

## 安装软件

如果您对所需软件没有特定要求，您可以使用 `pkg` 工具在 `FreeBSD` 上安装预编译包，它看起来类似于在 `GNU/Linux` 系统上使用 `yum` 或 `apt-get`。例如，在您的主机上安装 `python`：

```
# pkg install python 
......
===========================================================================

Note that some standard Python modules are provided as separate ports
as they require additional dependencies. They are available as:

bsddb           databases/py-bsddb
gdbm            databases/py-gdbm
sqlite3         databases/py-sqlite3
tkinter         x11-toolkits/py-tkinter

=========================================================================== 
```

现在你可以运行 `python` 了：

```
# python
Python 2.7.11 (default, Jun  5 2016, 01:23:11)
[GCC 4.2.1 Compatible FreeBSD Clang 3.4.1 (tags/RELEASE_34/dot1-final 208032)] on freebsd10
Type "help", "copyright", "credits" or "license" for more information.
>>> 
```

但是安装 `python` 后的结束日志提示我们仍然需要安装其他 `4` 个软件包：`py-bsddb`、`py-gdbm`、`py-sqlite3` 和 `py-tkinter`，否则 "`import sqlite3`" 将会报错：

```
>>> import sqlite3
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  File "/usr/local/lib/python2.7/sqlite3/__init__.py", line 24, in <module>
    from dbapi2 import *
  File "/usr/local/lib/python2.7/sqlite3/dbapi2.py", line 28, in <module>
    from _sqlite3 import *
ImportError: No module named _sqlite3 
```

这引入了另一种安装方法：使用端口。这种方法将从源代码下载、编译和安装，这种方法的好处是如果您愿意，您可以进行一些自定义。您可以在 `/usr/ports` 目录下找到所有端口。现在您开始安装 `py-bsddb`（按照此方法设置 `py-gdbm`、`py-sqlite3` 和 `py-tkinter`）：

```
# cd /usr/ports/databases/py-bsddb
# make install clean 
```

安装完所有软件后，我们现在可以在 `python` 中使用 `sqlite` 了：

```
# python
Python 2.7.11 (default, Jun  5 2016, 01:23:11)
[GCC 4.2.1 Compatible FreeBSD Clang 3.4.1 (tags/RELEASE_34/dot1-final 208032)] on freebsd10
Type "help", "copyright", "credits" or "license" for more information.
>>> import sqlite3 
```

另一种方法是从 `DVD` 安装：

(1) 将 `DVD` 放入驱动器中；

(2) 挂载 `DVD`：

```
mkdir -p /dist
mount -t cd9660 /dev/cd0 /dist 
```

(3) 安装包（例如，`xorg`）：

```
env REPOS_DIR=/dist/packages/repos pkg install xorg 
```

参考：

[软件包和端口：在 FreeBSD 中添加软件](https://www.freebsd.org/doc/en_US.ISO8859-1/articles/linux-users/software.html)；

[开始使用 FreeBSD：Linux 用户的简要介绍](http://www.infoworld.com/article/2858288/unix/intro-to-freebsd-for-linux-users.html)；

[FreeBSD 10 从 DVD 安装软件包](https://forums.freebsd.org/threads/44430/#post-300633)。
