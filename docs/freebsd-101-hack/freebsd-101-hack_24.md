# 在 csh 中向后搜索

## 在 csh 中向后搜索

在`bash`中，`Ctrl + R`提供了方便的“向后搜索”功能，默认情况下`csh`不提供该功能。如果你想在`csh`中使用类似的功能，可以使用`csh`内置的`bindkey`命令来实现：

```
# cat .cshrc
......

bindkey "^R" i-search-back 
```

当按下`Ctrl + R`时，你可以使用“向后搜索”功能：

```
root@FreeBSD:~ # pkg install subversion   
bck:pk 
```

参考资料：

[使用 Ctrl-R 在 csh 中向后搜索 shell 命令](http://stackoverflow.com/questions/1387357/ctrl-r-to-search-backwards-for-shell-commands-in-csh)。
