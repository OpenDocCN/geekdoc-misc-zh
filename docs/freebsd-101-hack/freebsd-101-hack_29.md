# 使用"procstat"获取进程信息

## 使用"procstat"获取进程信息

在`FreeBSD`上，你可以使用`procstat`命令获取进程的详细信息。例如：

```
# procstat 521
PID  PPID  PGID   SID  TSID THR LOGIN    WCHAN     EMUL          COMM
521     1   521   521     0   1 root     select    FreeBSD ELF64 syslogd 
```

上述输出描述了`PID`为`521`的进程的信息：它的`PID`、父进程的`PID`、命令名称等。

如果你想显示所有进程的信息，可以使用`-a`选项：

```
# procstat -a
PID  PPID  PGID   SID  TSID THR LOGIN    WCHAN     EMUL          COMM
0     0     0     0     0  10 -        -         -             kernel
1     0     1     1     0   1 root     wait      FreeBSD ELF64 init
2     0     0     0     0   2 -        -         -             cam
3     0     0     0     0   1 -        idle      -             mpt_recovery0
4     0     0     0     0   1 -        waiting_  -             sctp_iterator
5     0     0     0     0   2 -        umarcl    -             pagedaemon
6     0     0     0     0   1 -        psleep    -             vmdaemon
7     0     0     0     0   1 -        pgzero    -             pagezero 
```

你可以使用许多选项来使用`procstat`，比如，如果你对线程信息感兴趣，可以使用`-t`选项：

```
# procstat -t 521
PID    TID COMM             TDNAME           CPU  PRI STATE   WCHAN
521 100065 syslogd          -                  0  120 sleep   select 
```

想了解每个选项的详细信息，请参考[手册](https://www.freebsd.org/cgi/man.cgi?procstat)。
