# Sass

# 添加 libsass

Sass 及其端口 libsass 是领先的 CSS 预处理器，功能最丰富。但将 libsass 与 JavaScript 社区中的其他工具区分开的一点是，它不是用 JavaScript 编写的。实际上，它是用 C/C++编写的。因此，相同的库可移植到几乎任何可以编写包装器的语言中。到目前为止，最受欢迎的包装器是`node-sass`。

所有这些并不真的重要。唯一重要的是，这意味着我们需要经历一些额外的，尽管极其简单的设置步骤。

## 首先，让我们安装 Node-Sass：

```
$ npm install --save node-sass 
```

这将安装 Sass 的 Node 包装器和 C/C++ libsass 库。接下来，为了使 Grunt 能够使用该库，我们需要添加 Grunt-Sass 包。

```
$ npm install grunt-sass --save 
```

要将所有这些集成到项目中，我们只需更新`Gruntfile.js`。

```
module.exports = function(grunt) {
  grunt.initConfig({
    sass: {
      dist: {
        files: {
          'public/stylesheets/style.css': 'sass/style.scss'
        }
      }
    }
  });

  grunt.loadNpmTasks('grunt-sass');
  grunt.registerTask('default', ['sass']);
}; 
```

在`files:`对象中，您将列出输出 CSS 的路径，然后是输入 SCSS 文件的路径。

## 添加 Sass

要使其运行，我们需要添加`sass`目录并在其中放入`style.scss`文件。在项目的根目录中：

```
$ mkdir sass 
```

在`sass`目录中：

```
$ touch style.scss 
```

并添加以下 Sass 以便我们知道这个功能正常工作：

```
$color: orange;

body {
  background-color: $color;
} 
```

## 运行 Grunt

在这一点上，我们已经准备好运行`grunt`命令并处理一些 Sass 了。
