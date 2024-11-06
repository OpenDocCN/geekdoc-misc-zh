# 配置代理

# 配置代理

* * *

如果你的`FreeBSD`主机在代理后工作，你可能需要配置代理以使其访问网络。

对于`csh`或`tcsh`，在`/etc/csh.cshrc`中设置代理：

```
setenv HTTP_PROXY http://web-proxy.xxxxxx.com:8080
setenv HTTPS_PROXY https://web-proxy.xxxxxx.com:8080 
```

对于`sh`，在`/etc/profile`中设置代理：

```
export HTTP_PROXY http://web-proxy.xxxxxx.com:8080
export HTTPS_PROXY https://web-proxy.xxxxxx.com:8080 
```

参考：

[在受控网络中使用 FreeBSD - 必需的 HTTP 代理和无 FTP](http://www.rhyous.com/2012/04/13/using-freebsd-inside-a-controlled-network-a-required-http-proxy-and-no-ftp/)。
