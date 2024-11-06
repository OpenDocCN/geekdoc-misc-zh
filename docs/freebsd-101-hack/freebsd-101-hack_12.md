# 构建内核

## 构建内核

如果您想要自定义构建内核，您需要首先安装源代码（您可以参考此文）。然后进入您的机器的配置目录：

```
# cd /usr/src/sys/`uname -m`/conf 
```

复制一个新的内核配置文件：

```
# cp GENERIC NAN_FIRST_BUILD 
```

您可以根据需要修改新的配置文件（`NAN_FIRST_BUILD`）。

构建内核：

```
# cd /usr/src
# make buildkernel KERNCONF="NAN_FIRST_BUILD" 
```

一旦完成，安装新的内核二进制文件并重新启动：

```
# make installkernel KERNCONF="NAN_FIRST_BUILD"
# reboot 
```

检查内核版本，您会发现现在操作系统正在使用您新构建的内核：

```
# uname -a
FreeBSD FreeBSD 10.3-RELEASE-p5 FreeBSD 10.3-RELEASE-p5 #0: Tue Jul 19 17:52:57 CST 2016     root@FreeBSD:/usr/obj/usr/src/sys/NAN_FIRST_BUILD  amd64 
```

参考：

[在 FreeBSD 中构建自定义内核的方法](https://www.youtube.com/watch?v=KVNxaKu11F0)。
