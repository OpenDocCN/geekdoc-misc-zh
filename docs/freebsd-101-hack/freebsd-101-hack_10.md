# 移除软件

## 移除软件

在安装应用程序后，您可以使用"`pkg delete`"命令将其移除：

```
# pkg delete lsof
Checking integrity... done (0 conflicting)
Deinstallation has been requested for the following 1 packages (of 0 packages in the universe):

Installed packages to be REMOVED:
        lsof-4.90.b,8

Proceed with deinstalling packages? [y/N]: y
[1/1] Deinstalling lsof-4.90.b,8...
[1/1] Deleting files for lsof-4.90.b,8: 100% 
```

您还可以进入端口目录，并执行"`make deinstall`"指令：

```
# pwd
/usr/ports/sysutils/lsof
# make deinstall
===>  Deinstalling for lsof
===>   Deinstalling lsof-4.90.b,8
Updating database digests format: 100%
Checking integrity... done (0 conflicting)
Deinstallation has been requested for the following 1 packages (of 0 packages in the universe):

Installed packages to be REMOVED:
        lsof-4.90.b,8
[1/1] Deinstalling lsof-4.90.b,8...
[1/1] Deleting files for lsof-4.90.b,8: 100% 
```

参考：

[使用 Ports Collection](https://www.freebsd.org/doc/handbook/ports-using.html)。
