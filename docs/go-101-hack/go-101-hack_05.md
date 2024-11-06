# "go get"命令

## "go get"命令

"`go get`"命令是下载和安装包及其相关依赖项的标准方式，让我们通过一个示例来查看它的细节：

(1) 在 github 中创建一个[playstack](https://github.com/NanXiao/playstack)仓库；

(2) 在`playstack`文件夹中有一个`LICENSE`文件和一个`play`目录；

(3) `play`目录包括一个`main.go`文件：

```
package main

import (
    "fmt"
    "github.com/NanXiao/stack"
)

func main() {
    s := stack.New()
    s.Push(0)
    s.Push(1)
    s.Pop()
    fmt.Println(s)
} 
```

`main`包有一个依赖包：[stack](https://github.com/NanXiao/stack)。实际上，`main()`函数并没有执行任何有意义的操作，我们只是用这个项目作为一个示例。所以`playstack`的目录结构如下：

```
.
├── LICENSE
└── play
    └── main.go

1 directory, 2 files 
```

清理`$GOPATH`目录，并使用"`go get`"命令下载`playstack`：

```
# tree
.

0 directories, 0 files
# go get github.com/NanXiao/playstack
package github.com/NanXiao/playstack: no buildable Go source files in /root/gocode/src/github.com/NanXiao/playstack 
```

"`go get`"命令抱怨"`no buildable Go source files in ...`"，这是因为"`go get`"操作的对象是**包**，而不是**仓库**。在`playstack`中没有`*.go`源文件，因此它不是一个有效的包。

整理`$GOPATH`文件夹，并执行"`go get github.com/NanXiao/playstack/play`"：

```
# tree
.

0 directories, 0 files
# go get github.com/NanXiao/playstack/play
# tree
.
├── bin
│   └── play
├── pkg
│   └── linux_amd64
│       └── github.com
│           └── NanXiao
│               └── stack.a
└── src
    └── github.com
        └── NanXiao
            ├── playstack
            │   ├── LICENSE
            │   └── play
            │       └── main.go
            └── stack
                ├── LICENSE
                ├── README.md
                ├── stack.go
                └── stack_test.go

11 directories, 8 files 
```

我们可以看到不仅下载了`playstack`及其依赖项（`stack`），而且命令（`play`）和库（`stack`）都安装在了正确的位置。

"`go get`"命令背后的机制是它将获取包和依赖项的仓库（例如，使用"`git clone`"）。您可以通过"`go get -x`"来查看详细的工作流程：

```
# tree
.

0 directories, 0 files
# go get -x github.com/NanXiao/playstack/play
cd .
git clone https://github.com/NanXiao/playstack /root/gocode/src/github.com/NanXiao/playstack
cd /root/gocode/src/github.com/NanXiao/playstack
git submodule update --init --recursive
cd /root/gocode/src/github.com/NanXiao/playstack
git show-ref
cd /root/gocode/src/github.com/NanXiao/playstack
git submodule update --init --recursive
cd .
git clone https://github.com/NanXiao/stack /root/gocode/src/github.com/NanXiao/stack
cd /root/gocode/src/github.com/NanXiao/stack
git submodule update --init --recursive
cd /root/gocode/src/github.com/NanXiao/stack
git show-ref
cd /root/gocode/src/github.com/NanXiao/stack
git submodule update --init --recursive
WORK=/tmp/go-build054180753
mkdir -p $WORK/github.com/NanXiao/stack/_obj/
mkdir -p $WORK/github.com/NanXiao/
cd /root/gocode/src/github.com/NanXiao/stack
/usr/local/go/pkg/tool/linux_amd64/compile -o $WORK/github.com/NanXiao/stack.a -trimpath $WORK -p github.com/NanXiao/stack -complete -buildid de4d90fa03d8091e075c1be9952d691376f8f044 -D _/root/gocode/src/github.com/NanXiao/stack -I $WORK -pack ./stack.go
mkdir -p /root/gocode/pkg/linux_amd64/github.com/NanXiao/
mv $WORK/github.com/NanXiao/stack.a /root/gocode/pkg/linux_amd64/github.com/NanXiao/stack.a
mkdir -p $WORK/github.com/NanXiao/playstack/play/_obj/
mkdir -p $WORK/github.com/NanXiao/playstack/play/_obj/exe/
cd /root/gocode/src/github.com/NanXiao/playstack/play
/usr/local/go/pkg/tool/linux_amd64/compile -o $WORK/github.com/NanXiao/playstack/play.a -trimpath $WORK -p main -complete -buildid e9a3c02979f7c6e57ce4452278c52e3e0e6a48e8 -D _/root/gocode/src/github.com/NanXiao/playstack/play -I $WORK -I /root/gocode/pkg/linux_amd64 -pack ./main.go
cd .
/usr/local/go/pkg/tool/linux_amd64/link -o $WORK/github.com/NanXiao/playstack/play/_obj/exe/a.out -L $WORK -L /root/gocode/pkg/linux_amd64 -extld=gcc -buildmode=exe -buildid=e9a3c02979f7c6e57ce4452278c52e3e0e6a48e8 $WORK/github.com/NanXiao/playstack/play.a
mkdir -p /root/gocode/bin/
mv $WORK/github.com/NanXiao/playstack/play/_obj/exe/a.out /root/gocode/bin/play 
```

从上面的输出中，我们可以看到首先克隆了`playstack`仓库，然后是`stack`，最后执行编译和安装。

如果您只想下载源文件，而不编译和安装，可以使用"`go get -d`"命令：

```
# tree
.

0 directories, 0 files
# go get -d github.com/NanXiao/playstack/play
# tree
.
└── src
    └── github.com
        └── NanXiao
            ├── playstack
            │   ├── LICENSE
            │   └── play
            │       └── main.go
            └── stack
                ├── LICENSE
                ├── README.md
                ├── stack.go
                └── stack_test.go

6 directories, 6 files 
```

您也可以使用"`go get -u`"来更新包及其依赖项。

参考：

[Command go](https://golang.org/cmd/go/#hdr-Download_and_install_packages_and_dependencies);

[“go get”命令如何知道应该下载哪些文件？](https://groups.google.com/forum/#!topic/golang-nuts/-V9QR8ncf4w)。
