# 清晰的目录结构

## 清晰的目录结构

`FreeBSD`具有明确的基本操作系统和用户添加的应用程序之间的分离，这意味着所有不属于基本操作系统的内容都位于`/usr/local`目录下，而`/usr/local`目录包含的目录结构大部分与`/`或`/usr`目录中找到的结构相似。

例如，从端口树或`package`命令安装的应用程序将位于`/usr/local/bin`或`/usr/local/sbin`中，对应于`/bin`、`/sbin`、`/usr/bin`和`/usr/local/sbin`；`/etc`目录包含基本操作系统的配置文件，而`/usr/local/etc`包含用户添加的应用程序的配置文件。

参考资料：

[针对 Linux 用户的 FreeBSD 比较介绍](https://www.digitalocean.com/community/tutorials/a-comparative-introduction-to-freebsd-for-linux-users);

[目录结构](https://www.freebsd.org/doc/handbook/dirstructure.html);

[我喜欢 FreeBSD 的十件事情](https://bsdmag.org/download/the_begginers_guide/)。
