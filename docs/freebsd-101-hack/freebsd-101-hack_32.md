# 使用 Subversion 的注意事项

## 使用 Subversion 的注意事项

如果你想使用`Subversion`，比如更新端口树，你应该注意以下问题：

(1) 如果你的服务器在代理后面运行，你应该修改你的`Subversion`配置文件：

```
# cat ~/.subversion/servers
[global]
http-proxy-host = web-proxy.xxxx.com
http-proxy-port = 8080
http-compression = no 
```

否则，你可能会遇到以下错误：

```
# svn checkout https://svn.FreeBSD.org/ports/head /usr/ports
Error validating server certificate for 'https://svn.freebsd.org:443':
 - The certificate is not issued by a trusted authority. Use the
   fingerprint to validate the certificate manually!
 - The certificate hostname does not match.
Certificate information:
 - Hostname: FG3K6C3A15800021
 - Valid: from Mar 21 09:15:26 2015 GMT until Mar 21 09:15:26 2025 GMT
 - Issuer: FG3K6C3A15800021, Fortinet Ltd.
 - Fingerprint: 1D:F4:21:20:2F:06:41:45:3F:7A:18:FB:79:F3:BB:30:36:32:22:A3
(R)eject, accept (t)emporarily or accept (p)ermanently? p
svn: E170013: Unable to connect to a repository at URL 'https://svn.freebsd.org/ports/head'
svn: E000054: Error running context: Connection reset by peer 
```

或者：

```
# svn checkout https://svn.FreeBSD.org/ports/head /usr/ports
......
svn: E175002: REPORT request on '/ports/!svn/me' failed 
```

(2) 如果你遇到执行`svn`命令时出现类似以下错误：

```
svn: E200030: SQLite compiled for 3.11.1, but running with 3.9.2 
```

你应该更新你的`SQLite`：

```
# pkg upgrade sqlite3 
```

参考：

[在受控网络中使用 FreeBSD - 必须的 HTTP 代理和无 FTP](http://www.rhyous.com/2012/04/13/using-freebsd-inside-a-controlled-network-a-required-http-proxy-and-no-ftp/);

[如何为 svn 配置 HTTP 代理](http://stackoverflow.com/questions/1491180/how-to-configure-a-http-proxy-for-svn).
