# 将文件加载到内核并卸载

## 将文件加载到内核并卸载

你可以使用`kldload`命令将文件加载到内核中。例如，进入`/boot/kernel`目录，然后使用`kldstat`检查当前加载的文件：

```
# cd /boot/kernel
# kldstat
Id Refs Address            Size     Name
 1    6 0xffffffff80200000 17bc6a8  kernel
 2    1 0xffffffff81a11000 56c6     fdescfs.ko
 3    1 0xffffffff81a17000 2ba8     uhid.ko 
```

使用`kldload`加载`zfs.ko`文件：

```
# kldload zfs.ko
# kldstat
Id Refs Address            Size     Name
 1   15 0xffffffff80200000 17bc6a8  kernel
 2    1 0xffffffff81a11000 56c6     fdescfs.ko
 3    1 0xffffffff81a17000 2ba8     uhid.ko
 7    1 0xffffffff81a1a000 1ee0c8   zfs.ko
 8    1 0xffffffff81c09000 3330     opensolaris.ko 
```

你可以看到`zfs.ko`成功加载了。

卸载文件使用`kldunload`命令：

```
# kldunload zfs.ko
# kldstat
Id Refs Address            Size     Name
 1    6 0xffffffff80200000 17bc6a8  kernel
 2    1 0xffffffff81a11000 56c6     fdescfs.ko
 3    1 0xffffffff81a17000 2ba8     uhid.ko 
```

参考：

[kldload](https://www.freebsd.org/cgi/man.cgi?kldload(8));

[kldunload](https://www.freebsd.org/cgi/man.cgi?kldunload(8)).
