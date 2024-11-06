# Grunt

# 安装和设置 Grunt

Grunt 是 Node 世界的工作马。如果需要运行任务，那就让 Grunt 出马。如果你来自 Rails 世界，Grunt 就像是 make 或者 Rake。关于这个任务运行器有大量的文档，但在这个研讨会中，我将专注于让你快速上手应用程序的基础知识。

Grunt 的设置非常简单，只需在项目的根目录中创建一个新的`Gruntfile.js`文件，并添加以下 shell 语法：

```
module.exports = function(grunt) {
  grunt.initConfig({

    ...

  });

  grunt.loadNpmTasks('<package>');
}; 
```

要运行 Grunt，通常需要全局安装 Grunt：

```
npm install grunt -g 
```

但是等等！！部署呢？如果我们创建的任务需要在服务器上运行 Grunt，我们需要将其作为应用程序的依赖项。因此，让我们将其安装为本地依赖项：

```
npm install --save grunt 
```

使用这个基本结构和安装了 Grunt，我们现在可以开始为我们的应用程序添加新功能了。
