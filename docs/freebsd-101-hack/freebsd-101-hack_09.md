# 搜索软件

## 搜索软件

如果你想搜索特定的应用程序，可以使用"`pkg search`"命令。例如：

```
# pkg search lsof
lsof-4.90.b,8                  Lists information about open files (similar to fstat(1))
p5-Unix-Lsof-0.0.5_2           Unix::Lsof -- a wrapper to the Unix lsof utility 
```

如果你想知道软件在 ports 树中的路径，可以使用`-o`选项：

```
# pkg search -o lsof
sysutils/lsof                  Lists information about open files (similar to fstat(1))
sysutils/p5-Unix-Lsof          Unix::Lsof -- a wrapper to the Unix lsof utility 
```

如果 Ports 集合已经安装，你可以使用`whereis`命令：

```
# whereis lsof
lsof: /usr/local/sbin/lsof /usr/local/man/man8/lsof.8.gz /usr/ports/sysutils/lsof 
```

另一个巧妙的方法是使用"`echo`"命令：

```
# echo /usr/ports/*/*lsof*
/usr/ports/distfiles/lsof_4.90B.freebsd.tar.bz2 /usr/ports/sysutils/lsof 
```

参考：

[寻找软件](https://www.freebsd.org/doc/handbook/ports-finding-applications.html).
