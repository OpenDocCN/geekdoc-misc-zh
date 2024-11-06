# Sockstat 命令

## Sockstat 命令

在`FreeBSD`上，我们可以使用`sockstat`命令列出打开的互联网和`UNIX`域套接字：

```
# sockstat
USER     COMMAND    PID   FD PROTO  LOCAL ADDRESS         FOREIGN ADDRESS
root     sshd       45768 3  tcp4   192.168.80.129:22     192.168.80.1:60803
root     sshd       22144 3  tcp4   192.168.80.129:22     192.168.80.1:54834
root     sshd       19097 3  tcp4   192.168.80.129:22     192.168.80.1:58174
smmsp    sendmail   662   3  dgram  -> /var/run/log
root     sendmail   659   3  tcp4   127.0.0.1:25          *:*
root     sendmail   659   4  dgram  -> /var/run/logpriv
root     sshd       656   3  tcp6   *:22                  *:*
root     sshd       656   4  tcp4   *:22                  *:*
...... 
```

我们可以看到`sockstat`的输出列出了哪个进程拥有套接字，套接字的文件描述符号等信息。所以这是一个非常棒的工具来诊断与网络相关的问题。

参考：

[SOCKSTAT(1)](https://www.freebsd.org/cgi/man.cgi?query=sockstat&sektion=1).
