# 显示交换空间利用情况

## 显示交换空间利用情况

在 `FreeBSD` 上，你可以使用 `pstat -s` 来显示交换空间利用情况：

```
# pstat -s
Device          1K-blocks     Used    Avail Capacity
/dev/da0p3        1048540        0  1048540     0% 
```

还有另一种指定的 `swapinfo` 命令可用：

```
# swapinfo
Device          1K-blocks     Used    Avail Capacity
/dev/da0p3        1048540        0  1048540     0% 
```

你也可以以“人类可读”格式显示交换信息：

```
# swapinfo -h
Device          1K-blocks     Used    Avail Capacity
/dev/da0p3        1048540       0B     1.0G     0% 
```

或者以兆字节单位显示交换空间大小：

```
# swapinfo -m
Device          1M-blocks     Used    Avail Capacity
/dev/da0p3           1023        0     1023     0% 
```

参考：

[PSTAT](https://www.freebsd.org/cgi/man.cgi?query=swapinfo&sektion=8)。
