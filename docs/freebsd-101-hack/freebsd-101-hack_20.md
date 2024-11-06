# 修改 PATH 环境变量

## 修改 PATH 环境变量

在 `csh` 中，如果你想要改变 `$PATH` 环境变量，你应该修改 `.cshrc` 文件：

```
# cat .cshrc
......
set path = (/sbin /bin /usr/sbin /usr/bin /usr/games /usr/local/sbin /usr/local/bin $HOME/bin $HOME/gocode/bin)
...... 
```

例如，你将 "`/usr/local/go/bin`" 添加到 `$PATH` 中：

```
# cat .cshrc
......
set path = (/sbin /bin /usr/sbin /usr/bin /usr/games /usr/local/sbin /usr/local/bin $HOME/bin $HOME/gocode/bin /usr/local/go/bin)
...... 
```

执行 "`source .cshrc`" 命令，你会发现新的 `$PATH` 生效了：

```
# source .cshrc
# echo $PATH
/sbin:/bin:/usr/sbin:/usr/bin:/usr/games:/usr/local/sbin:/usr/local/bin:/root/bin:/root/gocode/bin:/usr/local/go/bin 
```

参考：

[杂项技巧和窍门](http://www.freebsdmadeeasy.com/tutorials/freebsd/freebsd-tricks.php)。
