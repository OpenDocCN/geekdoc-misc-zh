# 安装源代码

## 安装源代码

根据架构和版本下载`FreeBSD`源代码：

```
fetch ftp://ftp.freebsd.org/pub/`uname -s`/releases/`uname -m`/`uname -r | cut -d'-' -f1,2`/src.txz 
```

解压源代码包：

```
tar -C / -xvzf src.txz 
```

确保在`/etc/freebsd-update.conf`文件的`Components`行中包含`src`，这样当使用`freebsd-update`更新系统时，源代码也会被刷新。

```
# cat /etc/freebsd-update.conf
......
# Components of the base system which should be kept updated.
Components src world kernel
...... 
```

参考资料：

[关于下载 FreeBSD 内核代码的问题](https://lists.freebsd.org/pipermail/freebsd-questions/2016-July/272497.html)；

[安装 FreeBSD 后安装 freebsd 内核源代码](https://www.netroby.com/view/3595)。
