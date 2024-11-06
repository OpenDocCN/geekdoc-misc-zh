# 更新 Ports Collection

## 更新 Ports Collection

`/usr/ports` 下的内容被称为 Ports Collection，我们可以使用 `portsnap` 命令来更新它：

(1) 如果这是第一次使用 `portsnap`，您应该运行以下命令：

```
# portsnap fetch extract 
```

否则，您可能会遇到如下错误：

```
......
/usr/ports was not created by portsnap.
You must run 'portsnap extract' before running 'portsnap update'. 
```

(2) 从此，您只需执行 "`portsnap fetch update`" 即可更新 Ports Collection。

参考：

[使用 Ports Collection](https://www.freebsd.org/doc/handbook/ports-using.html);

[关于使用 portsnanp 升级 ports 树的问题](https://lists.freebsd.org/pipermail/freebsd-questions/2016-June/272255.html)。
