# 构建一个演示表单

# 创建一个消息表单：

### 逐步指南

从 0 到 60，构建一个联系小部件。

下面的演示是一个流行的 UI/UX 模式的重新设计，该模式在用户输入数据到表单时显示表单标签。

# 设置

# 设置 libsass

使用 Grunt Sass 安装 libsass 并添加 Bourbon。Node-Sass 作为 Grunt-Sass 的依赖项安装。

```
$ npm install grunt-sass --save
$ npm install node-bourbon --save 
```

## 添加 bower.json 文件

```
{
  "name": "class-demo",
} 
```

添加一些 Bower 包

```
$ bower install color-scale --save
$ bower install type-rhythm-scale --save
$ bower install rwd-toolkit --save 
```

## 安装 Grunt

```
npm install grunt --save 
```

## 安装 Grunt Watch

```
npm install grunt-contrib-watch --save-dev 
```

添加 `gruntfile.js`

```
module.exports = function(grunt) {
  grunt.initConfig({
    sass: {
      dist: {
        files: {
          'public/stylesheets/application.css': 'sass/application.scss'
        },
        options: {
          sourceMap: true,
          includePaths: [
            require('node-bourbon').includePaths,
            './bower_components/color-scale',
            './bower_components/type-rhythm-scale',
            './bower_components/rwd-toolkit'
          ]
        }
      }
    },
    watch: {
      source: {
        files: ['sass/**/*.scss', 'views/**/*.jade'],
        tasks: ['sass'],
        options: {
          livereload: true, // needed to run LiveReload
        }
      }
    }
  });

  grunt.loadNpmTasks('grunt-contrib-watch');
  grunt.loadNpmTasks('grunt-sass');
  grunt.registerTask('default', ['sass']);
}; 
```

## 创建新的 Sass 文件

创建以下目录和文件，然后向文件添加一些 Sass。

```
$ mkdir sass
$ touch sass/application.scss 
```

## 安装库依赖项

将这些添加到 `application.scss` 的清单中，以使 Sass 能够识别这些依赖项。

```
@import "bourbon";
@import "type-rhythm-scale";
@import "rwd-toolkit"; 
```

## 启动 Grunt

```
$ grunt
$ grunt watch 
```

# 版本控制

# 版本控制

添加 `.gitignore` 文件并添加以下内容：

```
# OS generated files
####################
.DS_Store
.DS_Store?
._*
.Spotlight-V100
.Trashes
ehthumbs.db
Thumbs.db

# Generated CSS output
#######################
public/stylesheets/*.css
public/stylesheets/*.css.map

# Package dependencies
######################
node_modules/
bower_components 
```

## 添加版本控制

```
$ git add --all
$ git commit -m "add all the things" 
```

# 布局

# 更新布局

更新 `layout.jade` 以使用 `application.css`

```
link(rel='stylesheet', href='/stylesheets/application.css') 
```

## 添加实时重新加载

```
script(src="//localhost:35729/livereload.js") 
```

刷新浏览器，然后开始对 Sass 和 Jade 文件进行小的编辑，以确保实时重新加载正常工作。

# 视图

# 构建视图

从布局开始，添加更多内容以使其正常工作

```
meta(charset='utf-8')
meta(http-equiv='X-UA-Compatible', content='IE=edge')
meta(name='description', content='#{description}')
meta(name='viewport', content='width=device-width, initial-scale=1.0, minimum-scale=0.5 maximum-scale=1.0 minimal-ui') 
```

更新 `./routes` 中的 `index.js` 文件

```
res.render('index', { title: 'Contact me', description: 'This is a new demo' }); 
```

打开 `./views/index.jade` 并添加以下内容：

```
section.message-container
  h1.title= title
  form#form.form(action='#', method='get')
    ul
      li
        label(for='name') Your Name:
        input#name(type='text', placeholder='Your Name', name='name', tabindex='1')
      li
        label(for='email') Your Email:
        input#email(type='email', placeholder='Your Email', name='email', tabindex='2')
      li
        label(for='message') Message:
        textarea#message(placeholder='Message…', name='message', tabindex='3')

    button#submit Send Message 
```

# UI 配置

# 构建 UI 配置文件

创建文件

```
$ touch _config.scss 
```

添加以下代码：

```
/////// Typography configuration
// *----------------------------------------
$font-size: 16;

$heading-1: 36;
$heading-2: 32;
$heading-3: 28;
$heading-4: 18;
$heading-5: 18;
$heading-6: 18;

$line: $font-size * 1.5;
$small-point-size: 10;
$large-point-size: 14;

$primary-font-family: #{"Helvetica Neue", Arial, sans-serif};
$secondary-font-family: #{"Helvetica Neue", Arial, sans-serif};
$heading-font-family: #{"Helvetica Neue", Arial, sans-serif};

/////// Default webfont directory
// *----------------------------------------
$fontDir: "fonts/";

/////// Default image directory
// *----------------------------------------
$imgDir: "images/";

/////// OOCSS generic base colors
// *----------------------------------------
$alpha-primary:   #5a2e2e;        // red
$bravo-primary:   #3e4147;        // green
$charlie-primary: #fffedf;        // yellow
$delta-primary:   #2a2c31;        // blue
$echo-primary:    #dfba69;        // accent

$alpha-gray:      #333;           //black

/////// Color math
// *----------------------------------------
@import "color-scale";

/////// Semantic variables
// *----------------------------------------
// abstract 'white' value to easily applied to semantic class objects
$white:                                #fff;

// primary header font color
$primary-header-color:                 $alpha-gray;

// default heading font weight
$heading-font-weight:                  normal;

// primary font color for the app
$primary-text:                         $alpha-gray;

// default `href` link color
$href-color:                           $delta-color;

// default shadow colors
$shadow-color:                         fade-out($alpha-color, 0.5);

// default border color
$border-color:                         $alpha-color;

/////// HTML 5 feature colors
// *----------------------------------------
// used with the `ins` tag
// http://www.w3schools.com/tags/tag_ins.asp
$ins-color:                            $charlie-color;

// used with the `mark` tag
// http://www.w3schools.com/html5/tag-mark.asp
$mark-color:                           $charlie-color;

// webkit tap highlight color
$webkit-tap-hightlight:                $delta-color;

// overrides the default content selection color in the browser
$selection-color:                      $charlie-color;
$selection-text-color:                 $primary-text;

//////// Default animation properties
// *----------------------------------------
$trans: .333s ease; 
```

在 `application.scss` 文件中添加

```
/////// App Config - this is where most of your magic will happen
// *----------------------------------------
@import "config"; 
```

# 重置

# 添加重置

添加文件

```
$ touch _reset.scss 
```

添加到 `application.scss`

```
/////// Standard CSS reset stuff here
// *-------------------------------------------------
@import "reset"; 
```

添加以下代码：

```
// * Let's default this puppy out
// *-------------------------------------------------

html, body, div, span, object, iframe, h1, h2, h3, h4, h5, h6, p, blockquote, pre, abbr, address, cite, code, del, dfn, em, img, ins, kbd, q, samp, small, strong, sub, sup, var, b, i, dl, dt, dd, ol, ul, li, fieldset, form, label, legend, table, caption, tbody, tfoot, thead, tr, th, td, article, aside, figure, footer, header, hgroup, menu, nav, section, menu, time, mark, audio, video {
  margin: 0;
  padding: 0;
  border: 0;
  vertical-align: baseline;
  background: transparent;
}

* {
  -moz-box-sizing: border-box;
  box-sizing: border-box;
}

body {
  font-size: 100%;
  -webkit-font-smoothing: antialiased;
}

article, aside, figure, footer, header, hgroup, nav, section {
  display: block;
}

// * Responsive images and other embedded objects
// * Note: keeping IMG here will cause problems if you're using foreground images as sprites, like, say for Google Maps custom placemarkers.
// * There has been a report of problems with standard Google maps as well, but we haven't been able to duplicate or diagnose the issue.

img, object, embed {
  max-width: 100%;
}

img {
  border-style: none;
  border-color: transparent;
  border-width: 0;
}

// * we use a lot of ULs that aren't bulleted.
// * don't forget to restore the bullets within content.

ol,ul {
  list-style: none;
}

blockquote, q {
  quotes: none;

  &:before, &:after {
    content: '';
    content: none;
  }
}

a {
  margin: 0;
  padding: 0;
  font-size: 100%;
  vertical-align: baseline;
  background: transparent;
  &:focus {
    text-decoration: underline ;
    outline: none;
  }
}

del {
  text-decoration: line-through;
}

pre {
  //white-space: pre
  // * CSS2
  white-space: pre-wrap;
  // * CSS 2.1
  //white-space: pre-line
  // * CSS 3 (and 2.1 as well, actually)
  word-wrap: break-word;
  // * IE
}

input {
  &[type="radio"] {
    vertical-align: text-bottom;
  }
}

input, textarea, select, button {
  font-family: inherit;
  font-weight: inherit;
  background-color: #fff;
  border: 0;
  padding: 0;
  margin: 0;
}

table {
  font-size: inherit;
}

sub, sup {
  font-size: 75%;
  line-height: 0;
  position: relative;
}

sup {
  top: -0.5em;
}

sub {
  bottom: -0.25em;
}

// * standardize any monospaced elements

pre, code, kbd, samp {
  font-family: monospace, sans-serif;
}

input {
  &[type=button], &[type=submit] {
    @extend %stipe-cursor-pointer;
  }
}

button {
  cursor: pointer;
  margin: 0;
  width: auto;
  overflow: visible;
}

a.button {
  display: inline-block;
}

// * scale images in IE7 more attractively

.ie7 img {
  -ms-interpolation-mode: bicubic;
}

// * Ok, this is where the fun starts.
// *-------------------------------------------------

a:link {
  -webkit-tap-highlight-color: $webkit-tap-hightlight;
}

ins {
  background-color: $ins-color;
  color: black;
  text-decoration: none;
}

mark {
  background-color: $mark-color;
  color: $primary-text;
  font-style: italic;
  font-weight: bold;
}

::selection {
  background: $selection-color;
  color: $selection-text-color;
}

::-moz-selection {
  background: $selection-color;
  color: $selection-text-color;
} 
```

# 全局布局 Sass

# 从全局布局开始

```
$ mkdir layouts
$ touch layouts/_global.scss
$ touch layouts/_manifest 
```

## 添加到 _global.scss

```
body {
  background-color: $delta-scale-juliet;
} 
```

## 添加到 application.scss

```
/////// Layouts
@import "layouts/manifest"; 
```

# 模块

# 创建一个模块

在 Sass 目录中，让我们创建一个包含必要文件的模块目录：

```
$ mkdir modules
$ mkdir modules/message-container
$ touch modules/message-container/_module-message-container.scss
$ touch modules/message-container/_manifest.scss 
```

在 `_module-message-container.scss` 文件中添加以下内容：

```
.message-container {
  margin: 1em auto;
  width: 90%;
  padding-bottom: 100px;
  @media #{$tablet} {
    width: 75%;
  }
  @media #{$desktop} {
    width: 50%;
  }
} 
```

## 添加到 _manifest.scss

```
@import "module-message-container"; 
```

## 添加到 application.scss

```
/////// Modules
@import "modules/message-container/manifest"; 
```

## 中央模块清单

在 `application.scss` 中，我们可以按照上述描述逐个输入每个模块，但我们也可以在 `modules` 的根目录下添加一个清单，该清单将导入其中包含的所有清单。

因此，在 `application.scss` 中我们做如下操作：

```
/////// Modules
@import "modules/manifest"; 
```

然后在 `modules/manifest.scss` 中执行此操作：

```
/////// Sub-Modules
@import "message-container/manifest"; 
```

这有助于保持事务更易于管理，因为我们永远不需要更新 `application.scss` 文件，并且在我们正在工作的模块目录的根目录中，我们只需添加一个新的清单即可。所有内容都被导入，一切都可以正常工作。

我们的文件夹结构将如下所示：

```
|- application.scss
|--- modules/
|----- _manifest.scss
|----- message-container/
|------- _manifest.scss
|------- _module-message-container.scss 
```

# 排版

# 排版

创建新的 sass 文件

```
$ touch _typography.scss 
```

添加以下代码：

```
html {
  font: em($font-size, 16) $primary-font-family;
  line-height: baseline($font-size);
  color: $primary-text
}

h1, h2, h3, h4, h5, h6, [role=heading] {
  @include heading();
}

.title {
  margin-bottom: em(5);
  padding: 0.25em 0;
  text-align: center;
  background-color: $delta-scale-bravo;
  color: $white;
  border-radius: em(5) em(5) 0 0;
} 
```

## 在 application.scss 的重置下面添加

```
/////// Base
@import "typography"; 
```

# 表单

# 表单

创建一个新的 sass 文件

```
$ touch _forms.scss 
```

创建一个新的 forms 目录

```
$ mkdir forms
$ midir forms/extends 
```

添加以下文件：

```
$ touch forms/_manifest.scss
$ touch forms/extends/_default-inputs.scss
$ touch forms/extends/_display-block.scss
$ touch forms/extends/_manifest.scss 
```

添加以下到 `forms/extends/_manifest.scss`：

```
@import "default-inputs";
@import "display-block"; 
```

添加到 `forms/extends/_default-inputs.scss`：

```
%default-inputs {
  width: 100%;
  height: 100%;
  padding: 2.25em 1em 1em;
  outline: none;
  font-size: 1em;
} 
```

添加到 `forms/extends/_display-block.scss`：

```
%display-block {
  width: 100%;
  display: block;
} 
```

添加以下到 `forms/_manifest.scss`：

```
@import "extends/manifest"; 
```

添加以下到 `_forms.scss`：

```
@import "forms/manifest";

.form {
  ul {
    border-bottom: 1px solid $hotel-gray;
    background-color: $white;
    margin-bottom: 1em;
  }
  li {
    border: 1px solid $hotel-gray;
    border-bottom: 0;
    position: relative;
  }
}

label {
  @extend %display-block;
  position: absolute;
  font-size: em(16);
  top: .5em;
  left: 1em;
  color: orange;
  opacity: 1;
  transition: #{$trans} top, #{$trans} opacity;
  .js-hide-label & {
    opacity: 0;
    top: 1.5em;
  }
}

input[type="text"] {
  @extend %display-block;
  @extend %default-inputs;
}

input[type="email"] {
  @extend %display-block;
  @extend %default-inputs;
}

textarea {
  @extend %display-block;
  @extend %default-inputs;
  height: 8em;
  resize: none;
} 
```

# 按钮

# 按钮

添加以下文件：

```
$ touch _buttons.scss 
```

在表单导入下添加到 `application.scss`

```
@import "buttons"; 
```

打开并添加以下代码：

```
button {
  @extend %default-inputs;
  -webkit-appearance: none;
  background: orange;
  color: white;
  border-radius: em(3);
  padding: 1em;
} 
```

# jQuery

# 添加一些 jQuery 魔法

打开`layout.jade`，在文档底部添加：

```
script(src='//ajax.googleapis.com/ajax/libs/jquery/1.11.0/jquery.min.js')
script(src="/javascripts/app.js") 
```

创建以下文件：

```
$ touch public/javascripts/app.js 
```

打开`app.js`，并添加以下内容：

```
// Test for placeholder support
$.support.placeholder = (function(){
  var i = document.createElement('input');
  return 'placeholder' in i;
})();

// Hide labels by default if placeholders are supported
if($.support.placeholder) {
  $('.form li').each(function(){
    $(this).addClass('js-hide-label');
  });
}

$('.form li').find('input, textarea').on('keyup blur focus', function(){

  // Cache our selectors
  var el = $(this),
    parent = el.parent();

    // Add or remove classes
    if( el.val() === '' ) {
        parent.addClass('js-hide-label');
    } else {
        parent.removeClass('js-hide-label');
    }
}); 
```
