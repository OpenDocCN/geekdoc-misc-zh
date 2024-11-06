# 升级到新版本

## 升级到新版本

本文以将系统从`10.2-RELEASE`升级到`10.3-RELEASE`为例，但请注意，此教程可能**不适用**于其他版本。因此，请阅读相关的发布说明。

(1) 检查当前版本：

```
# freebsd-version -ku
10.2-RELEASE
10.2-RELEASE 
```

(2) 运行"`freebsd-update upgrade`"命令将当前系统升级到新版本：

```
# freebsd-update upgrade -r 10.3-RELEASE
......
To install the downloaded upgrades, run "/usr/sbin/freebsd-update install". 
```

(3) "`freebsd-update upgrade -r 10.3-RELEASE`"的最后一个日志提示执行"`freebsd-update install`"：

```
# freebsd-update install
src component not installed, skipped
Installing updates...
Kernel updates have been installed.  Please reboot and run
"/usr/sbin/freebsd-update install" again to finish installing updates. 
```

(4) 重新启动系统，然后再次执行"`freebsd-update install`"：

```
# reboot
# freebsd-update install
src component not installed, skipped
Installing updates... done. 
```

(5) 现在检查版本：

```
# freebsd-version -ku
10.3-RELEASE-p4
10.3-RELEASE-p5 
```

系统现在已经升级到`10.3-RELEASE`。

参考：

[freebsd-update](https://www.freebsd.org/cgi/man.cgi?freebsd-update);

[FreeBSD 10.3-RELEASE 安装说明](https://www.freebsd.org/releases/10.3R/installation.html)。
