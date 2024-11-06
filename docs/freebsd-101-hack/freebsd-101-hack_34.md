# 挂载 procfs 文件系统

## 挂载 procfs 文件系统

`FreeBSD`默认不挂载`procfs`文件系统，如果需要，可以自行挂载：

```
mount -t procfs proc    /proc 
```

如果希望`procfs`在启动时自动挂载，可以在`/etc/fstab`文件中添加以下行：

```
proc         /proc   procfs  rw    0 0 
```

参考：

[procfs：已逝而不被遗忘](https://www.freebsd.org/doc/en/articles/linux-users/procfs.html)。

[procfs -- 进程文件系统](https://www.freebsd.org/cgi/man.cgi?query=procfs&sektion=&n=1)。
