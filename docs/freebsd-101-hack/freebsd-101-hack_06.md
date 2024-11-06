# 升级系统

## 升级系统

你应该利用"`freebsd-update`"实用程序来非周期性地升级你的系统，以保持系统的安全性和不陈旧。例如，在安装了一个新的`10.3`版本后：

```
# freebsd-version -ku
10.3-RELEASE
10.3-RELEASE 
```

你应该更新`FreeBSD`团队发布的补丁：

```
# freebsd-update fetch install 
```

当完成后，再次检查系统版本：

```
# freebsd-version -ku
10.3-RELEASE-p4
10.3-RELEASE-p5 
```

是的！你的系统已经刷新了！

参考资料：

[FreeBSD 手册页](https://www.freebsd.org/cgi/man.cgi?query=freebsd-update&sektion=8);

[在安装 FreeBSD 后我应该运行的第一批命令是什么？或者如何给 FreeBSD 打补丁？或者如何在 FreeBSD 上安装端口？](http://www.rhyous.com/2009/11/03/what-are-the-first-commands-i-run-after-installing-freebsd/)。
