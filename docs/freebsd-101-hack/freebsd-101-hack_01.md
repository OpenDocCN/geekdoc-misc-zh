# 获取系统版本

## 获取系统版本

FreeBSD 有 `2` 个版本：内核和用户空间。使用 "`freebsd-version -ku`" 可以输出两个版本：

```
# freebsd-version -uk
10.3-RELEASE-p4
10.3-RELEASE-p5 
```

第一个是内核版本信息。你可以看到内核和用户空间的版本都是`10.3`，但内核补丁级别是`p4`，而用户空间是`p5`。这是因为在某些情况下，只有用户空间需要补丁，而内核不需要，所以内核补丁级别不会改变。如果没有选项，"`freebsd-version`" 只会打印用户空间版本：

```
# freebsd-version
10.3-RELEASE-p5 
```

"`uname -r`" 命令也会输出内核版本：

```
# uname -r
10.3-RELEASE-p4 
```

参考：

[为什么“freebsd-version”和“freebsd-version -k”的输出结果会不同？](http://stackoverflow.com/questions/37800913/why-the-outputs-of-freebsd-version-and-freebsd-version-k-are-different)。
