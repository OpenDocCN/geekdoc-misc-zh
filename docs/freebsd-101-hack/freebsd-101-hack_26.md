# /var/run/dmesg.boot

## /var/run/dmesg.boot

`/var/run/dmesg.boot` 文件包含了 `FreeBSD` 的引导消息，对于检查硬件相关信息非常有帮助：

```
# cat /var/run/dmesg.boot | grep -i CPU
CPU: Intel(R) Core(TM) i5-4310U CPU @ 2.00GHz (2594.03-MHz K8-class CPU)
cpu0: <ACPI CPU> on acpi0 
```

由于系统消息缓冲区的容量有限，`FreeBSD` 在缓冲区内容被清空时使用 `/var/run/dmesg.boot`。

参考：

[设备和设备节点](https://www.freebsd.org/doc/handbook/basics-devices.html);

[回到基础：Unix 在执行任务时的差异](http://www.longitudetech.com/linux-unix/back-to-basics-unix-differences-in-performing-tasks/)。
