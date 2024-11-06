# 使用"freecolor"来显示内存和交换空间的使用情况

## 使用"freecolor"来显示内存和交换空间的使用情况

在`FreeBSD`上，`Freecolor`等同于`GNU/Linux`上的`free`。安装方法：

```
# cd /usr/ports/sysutils/freecolor
# make install clean 
```

以条形图格式显示内存和交换空间的使用情况：

```
# freecolor
Physical  : [#################################..] 94%   (1907820/2018396)
Swap      : [###################################] 100%  (1048540/1048540) 
```

以传统的"`free`"格式显示使用情况：

```
# freecolor -m -o
             total       used       free     shared    buffers     cached
Mem:          1971        107       1863          0          0          0
Swap:         1023          0       1023 
```

参考：

[FreeBSD 查找 RAM 大小，包括总的空闲和已用内存大小](http://www.cyberciti.biz/faq/freebsd-command-to-get-ram-information/)。
