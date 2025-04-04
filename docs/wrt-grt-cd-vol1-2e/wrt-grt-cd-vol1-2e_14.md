## 第十五章：**杂项输入输出设备**

![Image](img/comm1.jpg)

虽然大容量存储设备可以说是现代计算机系统中最常见的外设，但还有许多其他广泛使用的设备，例如通信端口（串口和并口）、键盘和鼠标以及声卡。这些外设将是本章的重点。

### 15.1 探索特定 PC 外设

从某些方面来看，讨论现代 PC 上的真实设备是危险的，因为传统的（“遗留”）设备几乎已经从 PC 设计中消失。随着制造商推出新款 PC，他们正在去除许多遗留的、易于编程的外设，如并口和串口，取而代之的是像 USB 和 Thunderbolt 这样的复杂外设。尽管本书并不涉及如何编程这些新型外设的详细讨论，但你需要了解它们的行为，以便编写出能够访问它们的优秀代码。

**注意**

*由于本章剩余部分讨论的外设的性质，所呈现的信息仅适用于 IBM 兼容 PC。由于本书篇幅所限，无法详细介绍不同系统上特定 I/O 设备的行为。其他系统支持类似的 I/O 设备，但其硬件接口可能与此处描述的不同。尽管如此，基本原则仍然适用。*

#### *15.1.1 键盘*

原始的 IBM PC 键盘本身就是一个计算机系统。键盘外壳内部埋藏着一个 8042 微控制器芯片，持续扫描键盘上的开关，检查是否有按键被按下。这一处理过程与 PC 的正常活动并行进行，即使 PC 的 80x86 处理器在忙于其他事务，键盘也从未错过任何一个按键。

一个典型的按键输入始于用户按下键盘上的一个键。这会关闭开关中的电接触点，键盘的微控制器可以感应到这一点。不幸的是，机械开关并不总是完美地关闭。通常，接触点在最终稳定连接之前会相互弹跳几次。对于不断读取开关的微控制器芯片来说，这些接触点的弹跳看起来像是一系列非常快速的按键按下和松开。如果微控制器将这些误认为多个按键输入，就会导致一个被称为*键盘弹跳*的现象，这个问题在许多便宜或老旧的键盘中很常见。即使在最昂贵和最新的键盘上，只要扫描频率足够高，键盘弹跳也可能成为问题，因为机械开关根本无法这么快速稳定。一个典型的便宜键通常需要 5 毫秒左右来稳定下来，因此如果键盘扫描软件的轮询频率低于这个值，控制器将有效地错过键盘弹跳。为了消除键盘弹跳，限制键盘扫描的频率这一做法被称为*去抖动*。典型的键盘控制器每 10 到 25 毫秒扫描一次键盘；低于这个频率可能会导致键跳动，而频率过高则可能会导致丢失按键输入（尤其是对于打字速度非常快的人）。

键盘控制器在每次扫描键盘并发现某个键被按住时，不应生成新的按键代码序列。用户可能会按住一个键很多毫秒，甚至几百毫秒才松开，我们不希望这被记录为多个按键输入。相反，键盘控制器应该在键从上升位置变为按下位置时（即*按键按下*操作）生成一个单一的按键代码值。此外，现代键盘提供了一个*自动重复*功能，一旦用户按住一个键超过一定时间（通常大约半秒钟），它会将按住的键视为一系列的按键输入，前提是用户继续按住该键。然而，即便是这些自动重复的按键输入也受到限制，每秒只能产生大约 10 次按键，而不是键盘控制器扫描所有键盘开关的频率。

在检测到按键按下事件后，微控制器会向 PC 发送一个键盘*扫描码*。扫描码*与*该键的 ASCII 码无关；它是 IBM 在最初开发 PC 键盘时选择的一个任意值。PC 键盘实际上会为每个按下的键生成*两个*扫描码。当按键被按下时，它会生成一个*按下码*，当键被释放时，它会生成一个*释放码*。如果用户长时间按住某个键，直到自动重复操作开始，键盘控制器会持续发送一系列的按下码，直到键被释放，此时键盘控制器会发送一个单一的释放码。

8042 微控制器芯片将这些扫描码传输到 PC，PC 通过*中断服务例程（ISR）*处理它们，处理的是键盘的输入。拥有单独的按下和松开码非常重要，因为某些键（如 SHIFT、CTRL 和 ALT）只有在按住时才有意义。通过为所有键生成松开码，键盘确保键盘 ISR 知道哪些键被按下，同时用户按住其中一个*修饰*键。系统如何处理这些扫描码取决于操作系统，但通常操作系统的键盘设备驱动程序会将扫描码序列转换为适当的 ASCII 码或其他应用程序可用的符号。

如今，几乎所有 PC 键盘都通过 USB 端口与计算机连接，并且它们可能使用比原始 IBM PC 键盘中使用的 8042 更现代的微控制器，但除此之外，它们的行为完全相同。

#### *15.1.2 标准 PC 平行端口*

原始的 IBM PC 设计提供了对三个并行打印机端口的支持（IBM 将其标记为*LPT1:*、*LPT2:*和*LPT3:*）。当时激光打印机和喷墨打印机仍然是几年的未来，IBM 可能预见到的是支持标准点阵打印机、波轮打印机，甚至可能是为不同目的设计的其他辅助类型打印机的机器。IBM 几乎可以肯定没有预见到并行端口的广泛使用，否则它可能会设计得不同。在鼎盛时期，PC 的并行端口控制了键盘、磁盘驱动器、磁带驱动器、SCSI 适配器、以太网和其他网络适配器、操纵杆适配器、辅助键盘设备、其他各种设备，以及哦，是的，打印机。

如今，由于连接器大小和性能问题，平行端口在大多数系统中已基本消失。然而，它仍然是一个有趣的设备。它是少数几个爱好者可以用来将 PC 与他们自己构建的简单设备连接起来的接口之一。因此，学习如何编程平行端口是许多硬件爱好者自发承担的任务。

在一个单向并行通信系统中，有两个不同的站点：发送站点和接收站点。发送站点将其数据放置在数据线上，并通知接收站点数据已就绪；接收站点随后读取数据线并通知发送站点它已接收数据。请注意，这两个站点是如何同步访问数据线的——接收站点在接收到发送站点的指示之前不会读取数据线，而发送站点在接收站点移除数据并告知发送站点它已接收数据之前不会在数据线上放置新值。换句话说，这种打印机与计算机系统之间的并行通信形式依赖于握手操作来协调数据传输。

计算机的并行端口除了八条数据线外，还使用三条控制信号实现握手。发送方使用*信号线*（或数据信号线）告知接收方数据可用。接收方使用*确认*线告诉发送方它已经接收了数据。第三条握手线，*忙碌*线，告诉发送方接收方正在忙碌，因此发送方不应尝试发送数据。忙碌信号与确认信号的不同之处在于，确认信号告诉系统接收方已经接受并*处理了*数据，而忙碌信号仅仅表示接收方暂时无法接收新数据——它并不意味着上一条数据传输已被处理（甚至已接收）。

在典型的数据传输会话中，发送方：

1.  检查忙碌线以查看接收方是否忙碌。如果忙碌线是激活的，发送方将在一个循环中等待直到忙碌线变为非激活状态。

1.  将数据放置在数据线上。

1.  激活信号线。

1.  在一个循环中等待直到确认线变为激活状态。

1.  设置信号线为非激活状态。

1.  在一个循环中等待接收方将确认线设置为非激活状态，表示它已识别信号线现在是非激活状态。

1.  对每个必须传输的字节，重复步骤 1 到 6。

与此同时，接收方：

1.  当接收方准备好接收数据时，设置忙碌线为非激活状态。

1.  在一个循环中等待直到信号线变为激活状态。

1.  从数据线读取数据。

1.  激活确认线。

1.  在一个循环中等待直到信号线变为非激活状态。

1.  设置忙碌线为激活状态（可选）。

1.  设置确认线为非激活状态。

1.  处理数据。

1.  设置忙碌线为非激活状态（可选）。

1.  对接收到的每个额外字节，重复步骤 2 到 9。

通过仔细遵循这些步骤，接收方和发送方协调各自的操作，确保发送方不会在接收方消费数据之前尝试将多个字节放到数据线上，且接收方不会在发送方未发送数据时尝试读取数据。

#### *15.1.3 串口*

RS-232 串行通信标准可能是世界上最受欢迎的串行通信方案。尽管它有许多缺点（速度是主要问题），但它被广泛使用，且有成千上万的设备可以通过 RS-232 串行接口连接到 PC。尽管许多设备仍在使用这一标准，但它正迅速被 USB 取代（如今你可以通过将 USB 转 RS-232 电缆插入 PC 来处理大多数 RS-232 接口需求）。

原始 PC 系统设计支持最多同时使用四个 RS-232 兼容设备，分别通过*COM1:*, *COM2:*, *COM3:* 和 *COM4:*端口连接。为了连接更多串行设备，你可以购买接口卡，允许你向 PC 添加 16 个或更多的串行端口。

在个人计算机的早期，DOS 程序员必须直接访问 8250 串行通信控制器（SCC）来实现其应用程序中的 RS-232 通信。一个典型的串行通信程序会有一个串行端口中断服务例程（ISR），它从 SCC 读取传入数据并将传出数据写入芯片，同时还包括初始化芯片以及缓冲传入和传出数据的代码。

幸运的是，今天的应用程序开发人员很少直接编程 SCC。相反，像 Windows 和 Linux 这样的操作系统提供了复杂的串行通信设备驱动程序，应用程序开发人员可以调用这些驱动程序。这些驱动程序提供了一套一致的功能集，所有应用程序都可以使用，这减少了实现串行通信功能所需的学习曲线。操作系统设备驱动程序方法的另一个优势是，它消除了对 8250 SCC 的依赖。使用操作系统设备驱动程序的应用程序将自动与不同的 SCC 配合工作。相比之下，直接编程 8250 的应用程序将无法在使用 USB 到 RS232 转换电缆的系统上工作。然而，如果该转换电缆的制造商为操作系统提供了合适的设备驱动程序，那么通过该操作系统进行串行通信的应用程序将自动与 USB/串行设备兼容。

对 RS-232 串行通信的深入研究超出了本书的范围。如需了解更多相关信息，请查阅操作系统程序员指南或阅读专门讨论此主题的许多优秀教材。

### 15.2 鼠标、触控板和其他指点设备

与磁盘驱动器、键盘和显示设备一起，指点设备可能是现代 PC 上最常见的外设之一。指点设备是外设中最简单的设备之一，提供给计算机一个非常简单的数据流。它们分为两类：一种是返回指针的相对位置，另一种是返回指点设备的绝对位置。*相对位置*是自上次系统读取设备以来的位置变化；*绝对位置*是固定坐标系统内的一组坐标值。鼠标、触控板和轨迹球返回相对坐标；触摸屏、光笔、压敏平板和操纵杆返回绝对坐标。

一般来说，将绝对坐标系统转换为相对坐标系统是容易的，但反过来则有问题。将相对坐标系统转换为绝对坐标系统需要一个常量的参考点，如果例如有人将鼠标从表面上抬起并放到另一个地方，这个参考点可能会变得毫无意义。幸运的是，大多数窗口系统使用来自指点设备的相对坐标值，因此返回相对坐标的指点设备的局限性不是问题。

早期的鼠标通常是光机械设备，旋转着两个沿鼠标主体 x 轴和 y 轴方向的编码轮。通常，两个轮子都会进行编码，每当它们移动一定距离时，发送 2 位脉冲。一个位告诉系统轮子已经移动了某个距离，另一个位告诉系统轮子的移动方向。^(1) 通过不断追踪来自鼠标的 4 位数据（每个轴 2 位），计算机系统可以确定鼠标的移动距离和方向，并在应用程序请求该位置时保持鼠标位置的非常精确记录。

让 CPU 追踪每次鼠标移动的一个问题是，当鼠标快速移动时，它会生成一个持续且高速的数据流。如果系统正在进行其他计算，它可能会错过一些传入的鼠标数据，从而导致丢失鼠标的位置。此外，主机的 CPU 时间最好用于应用程序计算，而不是跟踪鼠标位置。

结果，鼠标制造商很早就决定在鼠标内部集成一个简单的微控制器，以跟踪鼠标的物理运动，并响应系统对鼠标坐标更新的请求，或者至少在鼠标位置发生变化时定期生成中断。大多数现代鼠标通过 USB 连接到系统，并响应每大约 8 毫秒发生的系统请求的位置信息更新。

由于鼠标作为图形用户界面（GUI）指针设备被广泛接受，计算机制造商创造了许多其他设备来执行相同的功能，但更具便携性——例如，鼠标并不是最方便在旅行中连接到笔记本电脑的指针设备。轨迹球、应变计（许多笔记本电脑上*G*和*H*键之间的小“棒”）、触摸板、轨迹点和触摸屏都是制造商附加到笔记本电脑、平板电脑和个人数字助理（PDA）上的设备示例，以创建更便捷的指针设备。虽然这些设备在用户便利性上有所不同，但对操作系统来说，它们看起来都像鼠标。因此，从软件的角度来看，它们之间几乎没有区别。

在现代操作系统中，应用程序很少直接与指针设备进行交互。相反，操作系统跟踪鼠标的位置，并更新光标和其他鼠标效果，然后在发生某种指针设备事件（如按钮按下）时通知应用程序。作为对应用程序查询的响应，操作系统返回系统光标的位置和指针设备按钮的状态。

### 15.3 摇杆和游戏控制器

为 IBM PC 创建的模拟游戏适配器允许用户将最多四个电阻式电位器和四个数字开关连接到 PC 上。PC 游戏适配器的设计显然受到了 Apple II 计算机模拟输入功能的影响，Apple II 是当时最流行的计算机，也是 PC 开发时的参考。IBM 的模拟输入设计像 Apple 的一样，旨在保持极低的成本。准确性和性能根本不被关注。事实上，你可以以不到 3 美元的零售价格购买电子元件，自己组装一个游戏适配器。

由于直接读取原始 IBM PC 游戏控制器的电子元件存在固有的低效性，大多数现代游戏控制器在控制器内部包含将物理位置转换为数字值的模拟电子元件，并通过 USB 接口与系统连接。Microsoft Windows 和其他现代操作系统提供了一个特殊的游戏控制器设备驱动程序接口和 API，允许应用程序确定游戏控制器具有什么功能，并以标准化的形式将数据发送给这些应用程序。这使得游戏控制器制造商能够提供许多原始 PC 游戏控制器接口无法实现的特性。现代应用程序读取游戏控制器的数据，就像读取文件或其他字符型设备（如键盘）的数据一样。这大大简化了此类设备的编程，同时提高了整体系统性能。

一些“老派”的游戏程序员认为调用 API 本身就是低效的，认为伟大的代码总是直接控制硬件。这个观点有些过时，原因有几点。首先，大多数现代操作系统不允许应用程序直接访问硬件，即使程序员想要这样做。其次，直接与硬件通信的软件无法支持像让操作系统处理硬件那样广泛的设备。最后，大多数操作系统的设备驱动程序可能由硬件厂商或操作系统开发者的团队编写，比个人编写更为高效。

因为现代游戏控制器不再受限于原始 IBM PC 游戏控制卡的设计，它们提供了广泛的功能。有关如何为特定设备编程 API 的信息，请参考相关的游戏控制器和操作系统文档。

### 15.4 声卡

原始的 IBM PC 配备了内置扬声器，CPU 可以通过（使用板载定时器芯片）编程来产生单频音调。尽管可以产生各种各样的音效，但这需要编程控制直接连接到扬声器的一个单独位。这个过程几乎消耗了所有可用的 CPU 时间。在 PC 发布后的几年内，像 Creative Labs 这样的各大制造商创建了一种特殊的接口板——声卡——提供了更高质量的 PC 音频输出，并且消耗的 CPU 资源远远少于之前。

首批为 PC 设计的声卡并没有遵循任何标准，因为当时并不存在这样的标准。创意实验室（Creative Labs）的 Sound Blaster 声卡成为了事实上的标准，因为它具有合理的功能，并且销量极高。当时，并没有为声卡提供设备驱动程序，因此大多数应用程序都是直接编程访问声卡的寄存器。最初，很多应用程序都是为 Sound Blaster 声卡编写的，以至于任何想要使用大多数音频应用程序的人都必须购买这款声卡。其他声卡制造商很快模仿了 Sound Blaster 的设计，结果它们都被困在这个设计里，因为它们新增的任何功能都无法得到现有音频软件的支持。

声卡技术停滞不前，直到微软在 Windows 中引入了多媒体支持。最初的音频卡仅能进行中等质量的音乐合成，只能提供适用于视频游戏的低劣音效。一些卡片支持 8 位电话质量的音频采样，但音质显然不高保真。一旦 Windows 提供了一个标准化的、设备无关的音频接口，声卡制造商开始为 PC 生产高质量的声卡。

很快，出现了“CD 质量”的声卡，这些声卡能够以 44.1 KHz 和 16 位的质量录制和回放音频。更高质量的声卡开始加入*波表*合成硬件，能够实现更真实的乐器合成。像 Roland 和 Yamaha 这样的合成器制造商也推出了带有其高端合成器相同电子元件的声卡。如今，专业录音室使用基于 PC 的数字音频录音系统，以 24 位分辨率在 96 KHz（甚至 192 KHz）下录制原创音乐，毫无疑问，它们产生的效果优于大多数模拟录音系统。当然，这些系统的成本高达数千美元。它们绝对不是那种售价不到 100 美元的典型声卡。

#### *15.4.1 音频接口外设如何产生声音*

现代音频接口外设^(2)通常通过以下三种方式之一产生声音：模拟（FM 合成）、数字波表合成或数字回放。前两种方案产生音乐音调，是大多数基于计算机的合成器的基础，而第三种则用于回放数字录制的音频。

FM 合成方案是一种较老的、低成本的音乐合成机制，它通过控制音效卡上的各种振荡器和其他声音产生电路来创造音乐音调。这类设备产生的声音通常质量较低，令人联想到早期的视频游戏；无法将其误认为是真正的乐器。虽然一些低端音效卡仍将 FM 合成作为主要的声音生成机制，但现代音频外设很少再用它来生成除“合成”声音之外的任何声音。

现代音效卡提供的音乐合成功能通常采用波表合成技术：音频制造商通常会录制并数字化实际乐器的若干音符，然后将这些数字录音编程到只读存储器（ROM）中，并将其组装进音频接口电路中。当应用程序请求音频接口播放某个乐器的音符时，音频硬件会从 ROM 中回放录音，产生非常逼真的声音。

然而，波表合成并不仅仅是一个数字回放方案。为了录制超过 100 种不同乐器，每种乐器有几个八度音程范围，这将需要非常昂贵的 ROM 存储空间。因此，大多数此类设备的制造商会在音频接口卡上嵌入软件，通过改变几个八度音程的数字化波形来升高或降低音符。这使得制造商只需为每种乐器录制并存储一个八度音程（12 个音符）。一些合成器使用软件将单个录制的音符转换为任何其他音符，以降低成本，但制造商录制的音符越多，最终声音的质量就越好。一些高端音频卡会为复杂的乐器（如钢琴）录制多个八度音程，而对一些使用较少、结构较简单的声音产生物体（如枪声、爆炸声和人群噪音）只录制少数音符。

最后，纯数字回放有两个用途：回放任意音频录音和进行高端音乐合成，称为*采样*。采样合成器实际上是基于 RAM 的波表合成器版本。与将数字化乐器存储在 ROM 中不同，采样合成器将它们存储在系统 RAM 中。每当应用程序想要播放某个乐器的特定音符时，系统从系统 RAM 中提取该音符的录音，并将其发送到音频电路进行回放。像波表合成方法一样，采样合成器可以将数字化音符升降八度，但因为系统没有 ROM 中与字节成本相关的限制，音频制造商通常可以录制更多来自现实世界乐器的样本。一般来说，采样合成器提供麦克风输入，因此你可以自己创建样本。这使得你可以例如通过录制一只狗叫声并在合成器上生成几个八度的“狗叫”音符来演奏一首歌。第三方通常会出售包含流行乐器高质量样本的“音色库”。

纯数字回放的另一个用途是作为数字音频录音机。几乎所有现代声卡都有音频输入，理论上可以录制“CD 质量”的立体声音频。^(3) 这使得用户可以录制模拟信号并原样回放，像磁带录音机一样。借助足够的外部设备，甚至可以自己制作音乐录音并刻录自己的音乐 CD，尽管为了做到这一点，你需要比典型的 Sound Blaster 卡更高级的设备——至少像 DigiDesign ProTools HDX 或 M-Audio 系统那样先进的设备。

#### *15.4.2 音频和 MIDI 文件格式*

在现代 PC 中，回放声音的标准机制有两种：音频文件回放和 MIDI 文件回放。

音频文件包含数字化的声音样本以供回放。虽然有许多不同的音频文件格式（例如 WAV 和 AIF），基本原理是相同的——文件包含一些头部信息，指定录音格式（如 16 位 44.1 KHz 或 8 位 22 KHz）以及样本的数量，后面跟着实际的声音样本。一些较简单的文件格式允许在正确初始化声卡后，直接将数据传输到典型的声卡；其他格式可能在声卡处理数据之前需要进行少量数据转换。无论哪种情况，音频文件格式本质上是硬件独立版本的数据，通常是你会传输到通用声卡的数据。

声音文件的一个问题是它们可能会变得相当大。一分钟的立体声 CD 质量音频大约需要不到 10MB 的存储空间。一首典型的 3 到 4 分钟的歌曲需要 20MB 到 45MB 之间的存储空间。这样的文件不仅占用了大量的 RAM，还会消耗软件分发文件中相当一部分的存储空间。如果您播放的是您录制的独特音频序列，您别无选择，只能使用这些空间来存储该序列。然而，如果您播放的是由一系列重复声音组成的音频序列，您可以使用采样合成器所用的相同技术，仅存储每个声音的一个实例，然后使用某种索引值来指示您要播放的声音。这可以大大减小音乐文件的大小。

这正是*音乐仪器数字接口（MIDI）*文件格式的理念所在。MIDI 是一种控制音乐合成和其他设备的标准协议。如果您想播放没有人声或其他非音乐元素的音乐，MIDI 可以非常高效。

MIDI 文件与其存储音频样本不同，它仅指定播放的音乐音符、播放时间、播放时长、使用的乐器等等。由于只需几字节即可指定所有这些信息，因此 MIDI 文件可以非常紧凑地表示一整首歌。高质量的 MIDI 文件通常在 20KB 到 100KB 之间，适用于一首典型的 3 到 4 分钟歌曲。与之对比的是同样时长的音频文件需要 20MB 到 45MB。如今大多数声卡能够通过板载波形合成器或 FM 合成器播放*通用 MIDI（GM）*文件。大多数合成器制造商使用 GM 标准来控制其设备，因此其使用非常广泛，GM 文件也很容易获得。

MIDI 的一个问题是，播放质量取决于最终用户的声卡质量。一些较昂贵的音频板能够非常好地播放 MIDI 文件，但一些较低成本的音频板——包括不幸的是，许多将音频接口集成在主板上的系统——播放出来的声音就像卡通般的效果。

因此，您需要仔细考虑在应用程序中使用 MIDI。一方面，MIDI 具有文件较小和处理速度更快的优点。另一方面，在某些系统上，音频质量可能非常低，使得您的应用听起来很糟糕。您必须在这些方法的利弊之间找到适合您特定应用的平衡。

由于大多数现代声卡能够播放 CD 质量的录音，你可能会想知道为什么制造商不直接收集一堆样本并模拟这些采样合成器。实际上，他们做了。以 Roland 为例，它提供了虚拟音效画布程序，软件模拟其硬件 Sound Canvas 模块。这些虚拟合成器能够产生非常高质量的输出，但会消耗大量 CPU 能力，从而减少了应用程序可用的处理能力。如果你的应用程序不需要完全的 CPU 功能，这些虚拟合成器提供了一种非常高质量、低成本的解决方案。

如果你知道你的目标受众会使用合成器，另一种解决方案是通过 MIDI 接口端口将外部合成器模块连接到你的 PC，并将 MIDI 数据发送到合成器进行播放。这对于一个面向有限客户群的专业应用来说是一个可接受的解决方案，因为除了音乐人，很少有人会拥有合成器。

#### *15.4.3 音频设备编程*

现代应用程序中音频的一个最好的方面是音频的标准化程度非常高。文件格式和音频硬件接口在现代应用程序中非常容易使用。与大多数其他外设一样，很少有现代程序直接控制音频硬件，因为像 Windows 和 Linux 这样的操作系统提供了设备驱动程序来处理这些工作。在典型的 Windows 应用程序中产生声音所需的操作不多，仅需从包含声音信息的文件中读取数据，并将这些数据写入另一个由设备驱动程序使用的文件，后者再与实际的音频硬件进行交互。

在编写基于音频的软件时，另一个需要考虑的问题是你所使用的 CPU 是否具备多媒体扩展。奔腾及之后的 80x86 CPU 提供 MMX、SSE 和 AVX 指令集。其他 CPU 系列也提供类似的指令集扩展（例如，PowerPC 上的 AltiVec 指令或 ARM 上的 NEON）。虽然操作系统可能会在设备驱动程序中使用这些扩展指令，但你也可以在自己的应用程序中使用它们。不幸的是，这通常需要汇编语言编程，因为很少有高级语言能够高效地访问这些指令集。因此，如果你打算进行高性能的多媒体编程，汇编语言可能是你需要学习的内容。有关 Pentium SSE/AVX 指令集的更多细节，参见 *汇编语言的艺术*。

### 15.5 进一步了解

Axelson, Jan. *并行端口完全手册：编程、接口与使用 PC 的并行打印端口*。麦迪逊，威斯康星州：Lakeview 出版社，2000 年。

———. *串口完全手册：RS-232 和 RS-485 链接与网络的编程与电路*。麦迪逊，威斯康星州：Lakeview 出版社，2000 年。

Hyde, Randall. *汇编语言的艺术*。第二版。旧金山：No Starch Press，2010 年。
