# 模块 0x1 | 基础 Ruby Kung Fu

# 模块 0x1 | 基础 Ruby Kung Fu

Ruby 在处理字符串和数组场景时具有令人惊叹的能力和技巧。在本章中，我们将介绍一些在黑客生活中可能需要的技巧。

## 终端

### 终端大小

以下是从 Ruby 获取终端大小的几种不同方法：

+   通过 IO/console 标准库

```
require 'io/console'
rows, columns = $stdin.winsize
# Try this now
print "-" * (columns/2) + "\n" + ("|" + " " * (columns/2 -2) + "|\n")* (rows / 2) + "-" * (columns/2) + "\n" 
```

+   通过 readline 标准库

```
require 'readline'
Readline.get_screen_size 
```

+   通过环境，如 IRB 或 Pry

```
[ENV['LINES'].to_i, ENV['COLUMNS'].to_i] 
```

+   通过 tput 命令行

```
[`tput cols`.to_i , `tput lines`.to_i] 
```

## 具有制表符补全的控制台

我们无法停止嫉妒 Metasploit 控制台（msfconsole），在那里我们可以从命令行开关中休息一下。幸运的是，这里是在 Ruby 中进行控制台制表符补全的主要思想：

+   读取行

Readline 模块提供了 GNU Readline 的接口。此模块定义了一些方法，以便从 Ruby 解释器中完成并访问输入历史记录。

**console-basic1.rb**

```
#!/usr/bin/env ruby
# KING SABRI | @KINGSABRI
# 
require 'readline'

# Prevent Ctrl+C for exiting
trap('INT', 'SIG_IGN')

# List of commands
CMDS = [ 'help', 'rubyfu', 'ls', 'pwd', 'exit' ].sort

completion = proc { |line| CMDS.grep( /^#{Regexp.escape( line )}/ ) }

# Console Settings
Readline.completion_proc = completion        # Set completion process
Readline.completion_append_character = ' '   # Make sure to add a space after completion

while line = Readline.readline('-> ', true)
  puts line unless line.nil? or line.squeeze.empty?
  break if line =~ /^quit.*/i or line =~ /^exit.*/i
end 
```

现在运行它，试试制表符补全吧！

好吧，制表符补全的主要思想是使事情变得更容易，而不仅仅是“按制表符”。这里是一个简单的思路…

**console-basic2.rb**

```
require 'readline'

# Prevent Ctrl+C for exiting
trap('INT', 'SIG_IGN')

# List of commands
CMDS = [ 'help', 'rubyfu', 'ls', 'exit' ].sort

completion = 
    proc do |str|
      case 
      when Readline.line_buffer =~ /help.*/i
    puts "Available commands:\n" + "#{CMDS.join("\t")}"
      when Readline.line_buffer =~ /rubyfu.*/i
    puts "Rubyfu, where Ruby goes evil!"
      when Readline.line_buffer =~ /ls.*/i
    puts `ls`
      when Readline.line_buffer =~ /exit.*/i
    puts 'Exiting..'
    exit 0
      else
    CMDS.grep( /^#{Regexp.escape(str)}/i ) unless str.nil?
      end
    end

Readline.completion_proc = completion        # Set completion process
Readline.completion_append_character = ' '   # Make sure to add a space after completion

while line = Readline.readline('-> ', true)  # Start console with character -> and make add_hist = true
  puts completion.call
  break if line =~ /^quit.*/i or line =~ /^exit.*/i
end 
```

事情可能会更进一步，比如 *msfconsole*，也许？

* * *

+   [Ruby Readline 文档和教程](http://bogojoker.com/readline/)

# 字符串

# 字符串

## 为你的输出添加颜色

由于我们主要使用命令行，我们需要使输出更加优雅。以下是你可能需要的主要颜色。你总是可以添加到这个集合中。

```
class String
  def red; colorize(self, "\e[1m\e[31m"); end
  def green; colorize(self, "\e[1m\e[32m"); end
  def dark_green; colorize(self, "\e[32m"); end
  def yellow; colorize(self, "\e[1m\e[33m"); end
  def blue; colorize(self, "\e[1m\e[34m"); end
  def dark_blue; colorize(self, "\e[34m"); end
  def purple; colorize(self, "\e[35m"); end
  def dark_purple; colorize(self, "\e[1;35m"); end
  def cyan; colorize(self, "\e[1;36m"); end
  def dark_cyan; colorize(self, "\e[36m"); end
  def pure; colorize(self, "\e[0m\e[28m"); end
  def bold; colorize(self, "\e[1m"); end
  def colorize(text, color_code) "#{color_code}#{text}\e[0m" end
end 
```

你只需要在 `puts` 时调用颜色

```
puts "RubyFu".red
puts "RubyFu".green
puts "RubyFu".yellow.bold 
```

要理解这段代码，让我们用图表解释一下

```
\033  [0;  31m
 ^     ^    ^    
 |     |    |
 |     |    |--------------------------------------- [The color number]
 |     |-------------------- [The modifier]            (ends with "m")
 |-- [Escaped character]           | 0 - normal                     
     (you can use "\e")            | 1 - bold
                                   | 2 - normal again
                                   | 3 - background color
                                   | 4 - underline
                                   | 5 - blinking 
```

或者你可以使用一个名为 [colorized] 的外部 gem 来获取更多的选择

```
gem install colorize 
```

然后只需在脚本中引用它

```
require 'colorize' 
```

## 覆盖控制台输出

在你的终端中拥有更多的灵活性是很棒的，有时我们需要在我们的脚本中做更多的事情。

覆盖控制台输出可以使我们的应用程序更加优雅，对于像计数和加载进度条这样的重复输出，噪音更少。

我阅读了一个关于 [bash 提示符光标移动](http://www.tldp.org/HOWTO/Bash-Prompt-HOWTO/x361.html) 的教程，发现在我们的脚本中使用它很方便。这是我目前找到的内容

```
- Position the Cursor:
  \033[<L>;<C>H
     Or
  \033[<L>;<C>f
  puts the cursor at line L and column C.
- Move the cursor up N lines:
  \033[<N>A
- Move the cursor down N lines:
  \033[<N>B
- Move the cursor forward N columns:
  \033[<N>C
- Move the cursor backward N columns:
  \033[<N>D
- Clear the screen, move to (0,0):
  \033[2J
- Erase to end of line:
  \033[K
- Save cursor position:
  \033[s
- Restore cursor position:
  \033[u 
```

所以为了测试这些，我创建了以下 PoC

```
#!/usr/bin/env ruby
# KING SABRI | @KINGSABRI
(1..3).map do |num|
  print "\rNumber: #{num}"
  sleep 0.5
  print ("\033[1B")    # Move cursor down 1 line 

  ('a'..'c').map do |char|
    print "\rCharacter: #{char}"
    print  ("\e[K")
    sleep 0.5
    print ("\033[1B")    # Move cursor down 1 lines

    ('A'..'C').map do |char1|
      print "\rCapital letters: #{char1}"
      print  ("\e[K")
      sleep 0.3
    end
    print ("\033[1A")    # Move curse up 1 line

  end

  print ("\033[1A")    # Move curse up 1 line
end

print ("\033[2B")    # Move cursor down 2 lines

puts "" 
```

目前为止还不错，但是为什么不将这些作为 Ruby 方法来实现更加优雅的使用呢？所以我想到了以下内容

```
# KING SABRI | @KINGSABRI
class String
  def mv_up(n=1)
    cursor(self, "\033[#{n}A")
  end

  def mv_down(n=1)
    cursor(self, "\033[#{n}B")
  end

  def mv_fw(n=1)
    cursor(self, "\033[#{n}C")
  end

  def mv_bw(n=1)
    cursor(self, "\033[#{n}D")
  end

  def cls_upline
    cursor(self, "\e[K")
  end

  def cls
    # cursor(self, "\033[2J")
    cursor(self, "\e[H\e[2J")
  end

  def save_position
    cursor(self, "\033[s")
  end

  def restore_position
    cursor(self, "\033[u")
  end

  def cursor(text, position)
    "\r#{position}#{text}"
  end
end 
```

然后作为 PoC，我在同一个脚本中使用了相同的先前 PoC 代码（在运行时更新 String 类）

```
#!/usr/bin/env ruby
# KING SABRI | @KINGSABRI
# Level 1
(1..3).map do |num|
  print "\rNumber: #{num}"
  sleep 0.7
  # Level 2
  ('a'..'c').map do |char|
      print "Characters: #{char}".mv_down
      sleep 0.5
      # Level 3
      ('A'..'C').map do |char1|
          print "Capital: #{char1}".mv_down
          sleep 0.2
          print "".mv_up
      end
      print "".mv_up
  end
  sleep 0.7
end
print "".mv_down 3 
```

更加优雅，不是吗？请说是

一些应用程序…

### 创建进度百分比

```
(1..10).each do |percent|
  print "#{percent*10}% complete\r"
  sleep(0.5)
  print  ("\e[K") # Delete current line
end
puts "Done!" 
```

另一个例子

```
(1..5).to_a.reverse.each do |c|
  print "\rI'll exit after #{c} second(s)"
  print "\e[K"
  sleep 1
end 
```

使用我们优雅的方式（在运行时更新 String 类）

```
(1..5).to_a.reverse.each do |c|
  print "I'll exit after #{c} second".cls_upline
  sleep 1
end
puts 
```

* * *

# 转换

# 转换

字符串转换和/或编码是利用和防火墙绕过的重要部分。

## 将字符串/二进制转换为十六进制

如果不需要前缀，只需执行以下操作

```
"Rubyfu".unpack("H*")    #=> ["527562796675"] 
```

否则，请参见下面的方法

对于单个字符

```
'\x%02x' % "A".ord    #=> "\\x41" 
```

**注意：** 符号 `*""` 等于 `.join`

```
"ABCD".unpack('H*')[0].scan(/../).map {|h| '\x'+h }.join    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".unpack('C*').map { |c| '\x%02x' % c }.join    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".split("").map {|h| '\x'+h.unpack('H*')[0] }*""    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".split("").map {|c|'\x' + c.ord.to_s(16)}.join    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".split("").map {|c|'\x' + c.ord.to_s(16)}*""    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".chars.map {|c| '\x' + c.ord.to_s(16)}*""    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".each_byte.map {|b| b.to_s(16)}.join    #=> "41424344" 
```

或

```
"ABCD".each_char.map {|c| '\x'+(c.unpack('H*')[0])}.join    #=> "\\x41\\x42\\x43\\x44" 
```

或

```
"ABCD".chars.map {|c| '\x%x' % c.ord}.join    #=> "\\x41\\x42\\x43\\x44" 
```

## 将十六进制转换为字符串/二进制

```
["41424344"].pack('H*')    #=> ABCD 
```

或

```
"41424344".scan(/../).map { |x| x.hex.chr }.join    #=> ABCD 
```

或用于原始套接字

```
"41424344".scan(/../).map(&:hex).pack("C*")    #=> ABCD 
```

对于超出`.chr`范围的二进制情况。例如，你可能需要将 IP 地址转换为十六进制原始数据，然后通过套接字发送。仅仅将其转换为十六进制是行不通的

```
>> ip = "192.168.100.10"
=> "192.168.100.10"
>> ip.split(".").map {|c| '\x%02x' % c.to_i}.join 
=> "\\xc0\\xa8\\x64\\x0a" 
```

正如你所看到的，Ruby 读取返回`"\\xc0\\xa8\\x64\\x0a"`，这与`"\xc0\xa8\x64\x0a"`不相等。尝试直接在 irb 中输入这个值（带双引号）`"\xc0\xa8\x64\x0a"`，你会注意到返回值是`"\xC0\xA8d\n"`，这才是应该传递给原始套接字的值，而不是`"\\xc0\\xa8\\x64\\x0a"`。主要原因是 Ruby 转义了反斜杠（`\`）。

要解决这个问题，使用打包将整数转换为 8 位无符号（无符号字符）

```
ip.split(".").map(&:to_i).pack("C*")    #=> "\xC0\xA8d\n" 
```

**关于十六进制的注意事项：** 有时你可能会遇到非可打印字符，特别是在处理二进制原始数据时。在这种情况下，在文件顶部添加**(**`# -*- coding: binary -*-`**)**可以解决任何解释问题。

## 将十六进制（返回地址）转换为小端格式

小端格式就是简单地反转字符串，比如将"Rubyfu"反转为"ufybuR"，可以通过调用`String`类的`reverse`方法来实现

```
"Rubyfu".reverse 
```

在利用中，这并不像看起来那么简单，因为我们处理的是可能不代表可打印字符的十六进制值。

假设我们有`0x77d6b141`作为返回地址，我们想将其转换为小端格式以使 CPU 正确读取它。

一般来说，将`0x77d6b141`转换为`\x41\xb1\xd6\x77`是一个微不足道的任务，因为这是一个一次性过程，但如果你有一个需要在利用中分阶段的 ROP 链，情况就不同了。要做到这一点，只需将其作为数组`pack`

```
[0x77d6b141].pack('V') 
```

有时会因为非 Unicode 字符串问题而出现错误。要解决这个问题，只需强制编码为 UTF-8，但大多数情况下你不会遇到这个问题

```
[0x77d6b141].pack('V').force_encoding("UTF-8") 
```

如果你有一个 ROP 链，那么每次应用这个方法并不合适 - 所以你可以使用第一种方法，并在你的利用文件顶部添加**(**`# -*- coding: binary -*-`**)**。

## 转换为 Unicode 转义

**十六进制 Unicode 转义**

```
"Rubyfu".each_char.map {|c| '\u' + c.ord.to_s(16).rjust(4, '0')}.join 
```

或者使用解包

```
"Rubyfu".unpack('U*').map{ |i| '\u' + i.to_s(16).rjust(4, '0') }.join 
```

一个更短的方法

```
"Rubyfu".unpack('U*').map{ |i| "\\u00%x" % i }.join 
```

**八进制 Unicode 转义**

八进制转义与十六进��转义完全相同，只是我们将字符串转换为八进制而不是十六进制

```
"Rubyfu".each_char.map {|c| '\u' + c.ord.to_s(8).rjust(4, '0')}.join 
```

**双引号字符串中的转义序列**

```
"\u{52 75 62 79 66 75}" 
```

## 编码/解码 base-64 字符串

我们将以几种方式呈现这个问题。

**编码字符串**

```
["RubyFu"].pack('m0') 
```

或者

```
require 'base64'
Base64.encode64 "RubyFu" 
```

**解码**

```
"UnVieUZ1".unpack('m0') 
```

或者

```
 Base64.decode64 "UnVieUZ1" 
```

> **提示：**
> 
> 字符串解包方法对于将我们读取的数据作为字符串转换回其原始形式非常有用。要了解更多，请访问 www.ruby-doc.org/core/classes/String.html 上的 String 类参考。

## 编码/解码 URL 字符串

URL 编码/解码是众所周知的。从黑客的角度来看，我们经常需要它来处理客户端漏洞。

**编码字符串**

```
require 'uri'
puts URI.encode 'http://vulnerable.site/search.aspx?txt="><script>alert(/Rubyfu/.source)</script>' 
```

**解码字符串**

```
require 'uri'
puts URI.decode "http://vulnerable.site/search.aspx?txt=%22%3E%3Cscript%3Ealert(/Rubyfu/.source)%3C/script%3E" 
```

你可以编码/解码任何非 URL 字符串，当然。

上述方法仅对任何非 URL 标准字符串进行编码（例如`<>"{}`），但如果要对整个字符串进行编码，请使用`URI.encode_www_form_component`

```
puts URI.encode_www_form_component 'http://vulnerable.site/search.aspx?txt="><script>alert(/Rubyfu/.source)</script>' 
```

## HTML 编码/解码

**编码 HTML**

```
require 'cgi'
CGI.escapeHTML('"><script>alert("Rubyfu!")</script>') 
```

返回

```
&quot;&gt;&lt;script&gt;alert(&quot;Rubyfu!&quot;)&lt;/script&gt; 
```

**解码 HTML**

```
require 'cgi'
CGI.unescapeHTML("&quot;&gt;&lt;script&gt;alert(&quot;Rubyfu!&quot;)&lt;/script&gt;") 
```

返回

```
"><script>alert("Rubyfu!")</script> 
```

## 解码/编码 SAML 字符串

**解码 SAML**

```
# SAML Request 
saml = "fZJNT%2BMwEIbvSPwHy%2Fd8tMvHympSdUGISuwS0cCBm%2BtMUwfbk%2FU4zfLvSVMq2Euv45n3fd7xzOb%2FrGE78KTRZXwSp5yBU1hpV2f8ubyLfvJ5fn42I2lNKxZd2Lon%2BNsBBTZMOhLjQ8Y77wRK0iSctEAiKLFa%2FH4Q0zgVrceACg1ny9uMy7rCdaM2%2Bs0BWrtppK2UAdeoVjW2ruq1bevGImcvR6zpHmtJ1MHSUZAuDKU0vY7Si2h6VU5%2BiMuJuLx65az4dPql3SHBKaz1oYnEfVkWUfG4KkeBna7A%2Fxm6M14j1gZihZazBRH4MODcoKPOgl%2BB32kFz08PGd%2BG0JJIkr7v46%2BhRCaEpod17DCRivYZCkmkd4N28B3wfNyrGKP5bws9DS6PKDz%2FMpsl36Tyz%2F%2Fax1jeFmi0emcLY7C%2F8SDD0Z7dobcynHbbV3QVbcZW0TlqQemNhoqzJD%2B4%2Fn8Yw7l8AA%3D%3D"

require 'cgi'
require 'base64'
require 'zlib'

inflated = Base64::decode64(CGI.unescape(saml))
# You don't need below code if it's not deflated/compressed
zlib = Zlib::Inflate.new(-Zlib::MAX_WBITS)
zlib.inflate(inflated) 
```

返回

```
"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\r\n<samlp:AuthnRequest xmlns:samlp=\"urn:oasis:names:tc:SAML:2.0:protocol\" ID=\"agdobjcfikneommfjamdclenjcpcjmgdgbmpgjmo\" Version=\"2.0\" IssueInstant=\"2007-04-26T13:51:56Z\" ProtocolBinding=\"urn:oasis:names:tc:SAML:2.0:bindings:HTTP-POST\" ProviderName=\"google.com\" AssertionConsumerServiceURL=\"https://www.google.com/a/solweb.no/acs\" IsPassive=\"true\"><saml:Issuer xmlns:saml=\"urn:oasis:names:tc:SAML:2.0:assertion\">google.com</saml:Issuer><samlp:NameIDPolicy AllowCreate=\"true\" Format=\"urn:oasis:names:tc:SAML:2.0:nameid-format:unspecified\" /></samlp:AuthnRequest>\r\n" 
```

[来源](http://stackoverflow.com/questions/3253298/base64-decode64-in-ruby-returning-strange-results)

[关于 SAML 的更多信息][3]

* * *

[3]: [`dev.gettinderbox.com/2013/12/16/introduction-to-saml/`](http://dev.gettinderbox.com/2013/12/16/introduction-to-saml/)

# 提取

# 提取

字符串提取是所有程序员需要做的主要任务之一。这通常很困难，因为我们没有一个易于提取有用数据/信息的字符串呈现。以下是一些有用的 Ruby 字符串提取案例。

## 从网络中提取字符串

### 从字符串中提取 MAC 地址

我们需要从任意字符串中提取所有 MAC 地址

```
mac = "ads fs:ad fa:fs:fe: Wind00-0C-29-38-1D-61ows 1100:50:7F:E6:96:20dsfsad fas fa1 3c:77:e6:68:66:e9 f2" 
```

**使用正则表达式**

这个正则表达式应该支持 Windows 和 Linux 的 MAC 地址格式。

找到我们的 mac

```
mac_regex = /(?:[0-9A-F][0-9A-F][:\-]){5}[0-9A-F][0-9A-F]/i
mac.scan mac_regex 
```

返回

```
["00-0C-29-38-1D-61", "00:50:7F:E6:96:20", "3c:77:e6:68:66:e9"] 
```

### 从字符串中提取 IPv4 地址

我们需要从任意字符串中提取所有 IPv4 地址

```
ip = "ads fs:ad fa:fs:fe: Wind10.0.4.5ows 11192.168.0.15dsfsad fas fa1 20.555.1.700 f2" 
```

```
ipv4_regex = /(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)/ 
```

让我们找到我们的 IP 地址

```
ip.scan ipv4_regex 
```

返回

```
[["10", "0", "4", "5"], ["192", "168", "0", "15"]] 
```

### 从字符串中提取 IPv6 地址

```
 ipv6_regex = /^\s*((([0-9A-Fa-f]{1,4}:){7}([0-9A-Fa-f]{1,4}|:))|(([0-9A-Fa-f]{1,4}:){6}(:[0-9A-Fa-f]{1,4}|((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3})|:))|(([0-9A-Fa-f]{1,4}:){5}(((:[0-9A-Fa-f]{1,4}){1,2})|:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3})|:))|(([0-9A-Fa-f]{1,4}:){4}(((:[0-9A-Fa-f]{1,4}){1,3})|((:[0-9A-Fa-f]{1,4})?:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}))|:))|(([0-9A-Fa-f]{1,4}:){3}(((:[0-9A-Fa-f]{1,4}){1,4})|((:[0-9A-Fa-f]{1,4}){0,2}:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}))|:))|(([0-9A-Fa-f]{1,4}:){2}(((:[0-9A-Fa-f]{1,4}){1,5})|((:[0-9A-Fa-f]{1,4}){0,3}:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}))|:))|(([0-9A-Fa-f]{1,4}:){1}(((:[0-9A-Fa-f]{1,4}){1,6})|((:[0-9A-Fa-f]{1,4}){0,4}:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}))|:))|(:(((:[0-9A-Fa-f]{1,4}){1,7})|((:[0-9A-Fa-f]{1,4}){0,5}:((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}))|:)))(%.+)?\s*$/ 
```

+   [来源](https://github.com/rapid7/rex-socket/blob/master/lib/rex/socket.rb)

+   另请参阅

    +   [`gist.github.com/cpetschnig/294476`](https://gist.github.com/cpetschnig/294476)

    +   [`snipplr.com/view/43003/regex--match-ipv6-address/`](http://snipplr.com/view/43003/regex--match-ipv6-address/)

## 从网页中提取字符串

### 从文件中提取 URL

假设我们有以下字符串

```
string = "text here http://foo1.example.org/bla1 and http://foo2.example.org/bla2 and here mailto:test@example.com and here also." 
```

**使用正则表达式**

```
string.scan(/https?:\/\/[\S]+/) 
```

**使用标准 URI 模块**

这将返回一个 URL 数组

```
require 'uri'
URI.extract(string, ["http" , "https"]) 
```

### 从网页中提取 URL

使用上述技巧

```
require 'net/http'
URI.extract(Net::HTTP.get(URI.parse("http://rubyfu.net")), ["http", "https"]) 
```

或使用正则表达式

```
require 'net/http'
Net::HTTP.get(URI.parse("http://rubyfu.net")).scan(/https?:\/\/[\S]+/) 
```

### 从网页中提取电子邮件地址

```
email_regex = /\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,4}\b/i 
```

```
require 'net/http'
Net::HTTP.get(URI.parse("http://isemail.info/_system/is_email/test/?all")).scan(email_regex).uniq 
```

### 从 HTML 标签中提取字符串

假设我们有以下 HTML 内容，我们需要仅获取字符串并消除所有 HTML 标签

```
string = "<!DOCTYPE html>
<html>
<head>
<title>Page Title</title>
</head>
<body>

<h1>This is a Heading</h1>
<p>This is another <strong>contents</strong>.</p>

</body>
</html>"

puts string.gsub(/<.*?>/,'').strip 
```

返回

```
Page Title

This is a Heading
This is another contents. 
```

### 从文件中解析以冒号分隔的数据

在渗透测试期间，您可能需要解析具有以下非常常见格式的文本

```
description : AAAA
info : BBBB
info : CCCC
info : DDDD
solution : EEEE
solution : FFFF
reference : GGGG
reference : HHHH
see_also : IIII
see_also : JJJJ 
```

主要思想是删除*重复*键，并传递到一个具有值数组的键。

```
#!/usr/bin/env ruby
#
# KING SABRI | @KINGSABRI
# Usage:
#   ruby noawk.rb file.txt
#

file = File.read(ARGV[0]).split("\n")
def parser(file)
  hash = {} # Datastore
  splitter = file.map { |line| line.split(':', 2) }
  splitter.each do |k, v|
    k.strip! # remove leading and trailing whitespaces
    v.strip! # remove leading and trailing whitespaces

    if hash[k]      # if this key exists
      hash[k] << v  # add this value to the key's array
    else            # if not
      hash[k] = [v] # create the new key and add an array contains this value
    end
  end

  hash # return the hash
end

parser(file).each {|k, v| puts "#{k}:\t#{v.join(', ')}"} 
```

对于一行爱好者

```
ruby -e 'h={};File.read("text.txt").split("\n").map{|l|l.split(":", 2)}.map{|k, v|k.strip!;v.strip!; h[k] ? h[k] << v : h[k] = [v]};h.each {|k, v| puts "#{k}:\t#{v.join(", ")}"}' 
```

# 数组

# 数组

## 模式

#### 模式创建

假设模式长度=500（您可以将其更改为任何值）。默认情况下，这将创建 20280 个最大可能性。

```
pattern_create = ('Aa0'..'Zz9').to_a.join.each_char.first(500).join 
```

如果您需要更长的模式（例如 30000），可以执行以下操作

```
pattern_create = ('Aa0'..'Zz9').to_a.join
pattern_create = pattern_create  * (30000 / 20280.to_f).ceil 
```

#### 模式偏移

我假设模式等于或小于“20280”，我们正在寻找“9Ak0”模式字符。模式创建应从上面初始化

```
pattern_offset = pattern_create.enum_for(:scan , '9Ak0').map {Regexp.last_match.begin(0)} 
```

注意：这不考虑小端格式，对于这一点需要编写额外的代码。有关更多信息，请查看以下[代码][1]。

#### 从`\x00`到`\xff`生成所有十六进制值

```
puts (0..255).map {|b| ('\x%02X' % b)} 
```

> **注意：**
> 
> +   要将值表示从`\xea`更改为`0xea`，请将`\x%x`更改为`0x%x`
> +   
> +   要使所有字母大写（`\xea`到`\xEA`），将`\x%x`更改为`\x%X`

#### 生成所有可打印字符

```
(32..126).map {|c| c.chr} 
```

简短而不干净

```
(32..126).map &:chr 
```

* * *

[1]: [`github.com/KINGSABRI/BufferOverflow-Kit/blob/master/lib/pattern.rb`](https://github.com/KINGSABRI/BufferOverflow-Kit/blob/master/lib/pattern.rb)
