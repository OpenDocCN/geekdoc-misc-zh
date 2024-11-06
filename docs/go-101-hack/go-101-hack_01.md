# 如何搭建 Go 开发环境

# 如何搭建 Go 开发环境

* * *

在`Linux`操作系统下搭建`Go`开发环境总是很容易。以`Linux`操作系统为例（因为我是作为 root 用户登录的，所以如果您以非 root 用户登录，可能需要`sudo`来执行一些命令），您需要做的就是从[这里](https://golang.org/dl/)下载与您系统匹配的二进制包，然后解压缩它：

```
# wget https://storage.googleapis.com/golang/go1.6.2.linux-amd64.tar.gz
# tar -C /usr/local/ -xzf go1.6.2.linux-amd64.tar.gz 
```

现在，在`/usr/local`下有一个额外的`go`目录。搞定了！太容易了，对吧？是的，但还有一些收尾工作要做：

(1) 为了方便运行`Go`工具（`go`、`gofmt`等），您应该将`/usr/local/go`添加到`$PATH`环境变量中：

```
# cat /etc/profile  
......
PATH=$PATH:/usr/local/go/bin
export PATH 
...... 
```

(2) **强烈建议**在`*nix`下将`Go`安装在`/usr/local/go`目录下，在`Windows`下将`Go`安装在`c:\Go`目录下，因为这些默认目录已经嵌入了`Go`二进制发行版中。如果选择其他目录，您**必须**设置`$GOROOT`环境变量：

```
# cat /etc/profile  
......
GOROOT=/path/to/go
export GOROOT 
```

因此，只有在您将`Go`安装在自定义目录时才需要`$GOROOT`，而不是默认目录。

参考资料：

[开始](https://golang.org/doc/install);

[实际上您不需要设置 GOROOT](http://dave.cheney.net/2013/06/14/you-dont-need-to-set-goroot-really)。
