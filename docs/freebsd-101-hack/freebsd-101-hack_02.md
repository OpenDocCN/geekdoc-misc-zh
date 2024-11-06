# 启用 SSH 上的 root 登录

# 启用 SSH 上的 root 登录

* * *

默认情况下，`FreeBSD` 主机不允许 `root` 用户通过 `SSH` 登录，要启用它，您需要修改 `SSH` 守护程序配置文件（`/etc/ssh/sshd_config`）。

更改以下行：

```
#PermitRootLogin no 
```

为：

```
PermitRootLogin yes 
```

然后重新启动 `SSH` 守护程序：

```
# /etc/rc.d/sshd restart 
```

参考：

[如何在 FreeBSD 8.2 上启用 root 登录](http://blog.bobbyallen.me/2011/07/22/how-to-enable-root-login-over-ssh-on-freebsd-8-2/)。 
