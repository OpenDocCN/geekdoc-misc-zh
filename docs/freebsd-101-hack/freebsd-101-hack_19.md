# 更改 shell

## 更改 shell

如果你之前在`Linux`上工作，可能会错过`Bash`，并且不习惯`FreeBSD`默认安装的`csh`。你可以按照以下说明将 shell 更改为`Bash`：

(1) `Bash`必须已经安装在你的`FreeBSD`上，并且其完整路径也应包含在`/etc/shells`中。例如：

```
 # pkg install bash
Updating FreeBSD repository catalogue...
FreeBSD repository is up-to-date.
All repositories are up-to-date.
The following 1 package(s) will be affected (of 0 checked):

New packages to be INSTALLED:
        bash: 4.3.42_1
...... 
```

然后你会发现`Bash`的路径已经自动出现在`/etc/shells`中：

```
 # cat /etc/shells
# $FreeBSD: releng/10.3/etc/shells 59717 2000-04-27 21:58:46Z ache $
#
# List of acceptable shells for chpass(1).
# Ftpd will not allow users to connect who are not using
# one of these shells.

/bin/sh
/bin/csh
/bin/tcsh
/usr/local/bin/bash
/usr/local/bin/rbash 
```

(2) 执行`chsh -s /usr/local/bin/bash`：

```
# chsh -s /usr/local/bin/bash
chsh: user information updated 
```

重新登录后，你会发现 shell 现在是`bash`了：

```
# echo $SHELL
/usr/local/bin/bash 
```

参考：

[Shells](https://www.freebsd.org/doc/handbook/shells.html)。
