# 安装 bash-completion

## 安装 bash-completion

[bash-completion](https://github.com/scop/bash-completion) 是一个非常方便的工具，可以帮助你自动完成许多命令，比如 `git`。要使用它，你需要 `2` 个步骤：

(1) 安装它：

```
pkg install bash-completion 
```

(2) 在你的 `~/.profile` 中添加以下命令：

```
[[ $PS1 && -f /usr/local/share/bash-completion/bash_completion.sh ]] && \
        source /usr/local/share/bash-completion/bash_completion.sh 
```
