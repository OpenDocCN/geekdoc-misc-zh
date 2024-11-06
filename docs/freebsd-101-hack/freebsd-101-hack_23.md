# 重新哈希命令

## 重新哈希命令

从 `$PATH` 变量列出的目录中删除应用程序后，甚至在输入前几个字符时，您可能会看到命令提示符：

```
# pkg delete lsof
Checking integrity... done (0 conflicting)
Deinstallation has been requested for the following 1 packages (of 0 packages in the universe):

Installed packages to be REMOVED:
        lsof-4.90.b,8

Proceed with deinstalling packages? [y/N]: y
[1/1] Deinstalling lsof-4.90.b,8...
[1/1] Deleting files for lsof-4.90.b,8: 100%
# ls
ls        ls-F      lsextattr lsof      lspci     lsvfs 
```

在运行时一定会提示 "`命令未找到。`"：

```
# lsof
lsof: Command not found. 
```

无论是安装还是移除应用程序，您都需要在 `csh` 中运行 `rehash` 命令，以使 shell 重新计算命令所在的表。

参考：

[杂项提示和技巧](http://www.freebsdmadeeasy.com/tutorials/freebsd/freebsd-tricks.php)；

[重新哈希](http://www.panix.com/~spkemp/examplex/csh/rehash.htm)。
