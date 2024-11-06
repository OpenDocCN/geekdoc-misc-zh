# 安装和使用 F#

F# 编译器是一个免费的开源工具，可用于 Windows、Mac 和 Linux（通过 Mono）。了解更多关于 F# 以及如何安装它的信息，请访问[F# 基金会](http://fsharp.org/)。

你可以在 IDE（Visual Studio、MonoDevelop）中使用它，或者在你喜欢的编辑器中使用它（VS Code 和 Atom 使用[Ionide](http://ionide.io/)具有特���好的 F# 支持），或者简单地作为一个独立的命令行编译器。

如果你不想安装任何东西，你可以尝试[.NET Fiddle](https://dotnetfiddle.net/)网站，这是一个交互式环境，你可以在网页浏览器中探索 F#。你应该能够在那里运行这个网站上的大部分代码。

## 使用代码示例

一旦你安装并运行了 F#，你就可以跟着代码示例进行学习。

在这个网站上运行代码示例的最佳方法是将代码输入到一个`.FSX`脚本文件中，然后将其发送到 F# 交互窗口进行评估。或者你可以直接将示例输入到 F# 交互控制台窗口中。除了一两行代码之外，我建议使用脚本文件的方法。

对于较长的示例，代码可以从这个网站下载 -- 链接将在帖子中提供。

最后，我鼓励你玩弄和修改这些示例。如果你遇到编译器错误，请查看"F# 故障排除"页面，该页面解释了最常见的问题以及如何解决它们。

## 项目和解决方案

F# 使用与 C# 相同的“项目”和“解决方案”模型，因此如果你熟悉这一点，你应该能够很容易地创建一个 F# 可执行文件。

要创建一个将作为项目的一部分编译的文件，而不是脚本文件，请使用`.fs`扩展名。`.fsx`文件不会被编译。

与 C# 相比，F# 项目确实有一些主要区别：

+   F# 文件是*线性*组织的，而不是以文件夹和子文件夹的层次结构组织。事实上，在 F# 项目中没有“添加新文件夹”的选项！这通常不是问题，因为与 C# 不同，一个 F# 文件包含多个类。在 C# 中可能是一个文件夹的整个类，而在 F# 中可能很容易成为一个单独的文件。

+   项目中文件的*顺序非常重要*：一个“后来”的 F# 文件可以使用在“先前”的 F# 文件中定义的公共类型，但反之则不行。因此，文件之间不能有循环依赖关系。

+   你可以通过右键单击并选择“上移”或“下移”来更改文件的顺序。同样，在创建新文件时，你可以选择在现有文件的“上方添加”或“下方添加”。

## 在 F# 中的 Shell 脚本

你也可以将 F# 用作脚本语言，而不必将代码编译成 EXE。这是通过使用 FSI 程序来实现的，它不仅是一个控制台，还可以用于运行脚本，就像你可能会使用 Python 或 Powershell 一样。

当您想快速创建一些代码而不将其编译成完整的应用程序时，这非常方便。F#构建自动化系统["FAKE"](https://github.com/fsharp/FAKE)就是一个展示这种用途有多有用的例子。

要了解如何自己做到这一点，这里有一个小例子脚本，可以将网页下载到本地文件。首先创建一个 FSX 脚本文件 -- 叫做"`ShellScriptExample.fsx`" -- 然后粘贴以下代码。

```
// ================================
// Description: 
//    downloads the given url and stores it as a file with a timestamp
//
// Example command line: 
//    fsi ShellScriptExample.fsx http://google.com google
// ================================

// "open" brings a .NET namespace into visibility
open System.Net
open System

// download the contents of a web page
let downloadUriToFile url targetfile =        
    let req = WebRequest.Create(Uri(url)) 
    use resp = req.GetResponse() 
    use stream = resp.GetResponseStream() 
    use reader = new IO.StreamReader(stream) 
    let timestamp = DateTime.UtcNow.ToString("yyyy-MM-ddTHH-mm")
    let path = sprintf "%s.%s.html" targetfile timestamp 
    use writer = new IO.StreamWriter(path) 
    writer.Write(reader.ReadToEnd())
    printfn "finished downloading %s to %s" url path

// Running from FSI, the script name is first, and other args after
match fsi.CommandLineArgs with
    | [| scriptName; url; targetfile |] ->
        printfn "running script: %s" scriptName
        downloadUriToFile url targetfile
    | _ ->
        printfn "USAGE: [url] [targetfile]" 
```

不要担心代码现在是如何工作的。它相当粗糙，一个更好的示例会添加错误处理等功能。

要运行此脚本，请在相同目录中打开一个命令窗口并输入：

```
fsi ShellScriptExample.fsx http://google.com google_homepage 
```

当您在这个网站上玩弄代码时，您可能想尝试同时创建一些脚本。
