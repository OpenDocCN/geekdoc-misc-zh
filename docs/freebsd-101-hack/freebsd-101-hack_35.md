# Kldstat 命令

## Kldstat 命令

在`FreeBSD`中，你可以使用`kldstat`命令来显示动态链接到内核中的任何文件的状态：

```
# kldstat
Id Refs Address            Size     Name
 1    6 0xffffffff80200000 17bc6a8  kernel
 2    1 0xffffffff81a11000 56c6     fdescfs.ko
 3    1 0xffffffff81a17000 2ba8     uhid.ko 
```

如果你想要更详细的信息，可以使用`-v`选项：

```
# kldstat -v
Id Refs Address            Size     Name
 1    6 0xffffffff80200000 17bc6a8  kernel (/boot/kernel/kernel)
 Contains modules:
  Id Name
  386 if_lo
  398 newreno
  373 elf32
  372 elf64
  374 shell
..... 
```

参考：

[KLDSTAT(8)](https://www.freebsd.org/cgi/man.cgi?kldstat(8))。
