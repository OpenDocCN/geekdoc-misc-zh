# 在 `csh` 中修剪文件

## 在 `csh` 中修剪文件

在 `bash` 中，如果你想要清空一个文件，最简单的命令可能是 "`> file`"：

```
# cat test.txt
Hello world!
# > test.txt
# cat test.txt
# 
```

但在 `csh` 中，"`> file`" 会导致 "`Invalid null command.`" 错误：

```
# cat test.txt
Hello world!
# > test.txt
Invalid null command. 
```

解决方法是使用 "`: > file`" 命令：

```
# cat test.txt
Hello world!
# : > test.txt
# cat test.txt
# 
```

或者使用 "`cat /dev/null > file`"。

参考：

[脚本中前导冒号（:）代表什么？](http://aplawrence.com/Basics/leading-colon.html)。
