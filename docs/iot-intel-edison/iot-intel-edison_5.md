# 分析

# 分析

+   [物联网分析 Top 20 IoT 公司](http://iot-analytics.com/top-20-iot-companies-q2-2015/)

# 在线培训

# 在线培训

# Coursera，物联网和嵌入式系统简介

> “物联网”的爆炸式增长正在改变我们的世界，Typical IoT 组件价格的快速下降使人们可以在家中创新设计和产品。在这个专业的第一堂课中，您将了解物联网在社会中的重要性，Typical IoT 设备的当前组件以及未来的趋势。还将涵盖物联网设计考虑因素、约束和物理世界与您的设备之间的接口。您还将学习如何在硬件和软件之间做出设计权衡。我们还将介绍网络的关键组成部分，以确保学生了解如何将其设备连接到互联网。[物联网和嵌入式系统简介](https://www.coursera.org/learn/iot/home/welcome)

[物联网](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/InternetOfThings.html)部分

**指导** 完成所有“物联网和嵌入式系统简介”

+   模块 1 什么是物联网（IoT）？

    +   第一课：物联网（IoT）定义

    +   第二课：物联网（IoT）采用趋势

    +   第三课：物联网（IoT）在社会中的重要性

+   模块 2 嵌入式系统

    +   第一课：嵌入式系统的特性和约束

    +   第二课：嵌入式系统组件

    +   第三课：与物理世界互动

+   模块 3 硬件和软件

    +   第一课：硬件组件

    +   第二课：微控制器和软件

    +   第三课：操作系统

+   模块 4 网络和互联网

    +   第一课：网络基础知识

    +   第二课：Internet 协议

    +   第三课：网络层和 MANETS

# 挑战

# 挑战

通过这个逐步挑战，您将获得物联网的并行学习体验，并在研讨会期间构建的项目上继续实现功能。

1.  数据报告，系统数据，设备标识

1.  数据报告，系统通信协议，设备标识

1.  数据报告，系统通信协议，RESTFul API

1.  数据报告，云计算服务，freeboard.io 和 dweet.io

1.  数据报告，云计算服务，adafruit.io

1.  数据报告，云计算平台，IBM Watson IoT 平台

1.  物理传感器（Seeed Studio Grove 套件）

1.  软件版本控制系统推送代码

# 01 数据报告，系统数据，设备标识

[系统数据](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/Data.html)部分

**指导**

> 定义全局变量“DeviceID”作为您物联网设备的唯一设备标识

# 02 数据报告，系统通信协议，设备标识

章节 [系统通信协议](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/platform/Protocols.html)

**指导**

> 在你的 MQTT 发布和订阅主题 IoT101/**DeviceID**/# 下包含你的 "**DeviceID**" 全局变量

需要更改 2 个函数中的代码：

+   functionDataSensorMqttPublish

+   functionDataActuatorMqttSubscribe

这里是新代码可能看起来的样子：

```
#!/usr/bin/python

import paho.mqtt.client as paho
...
def functionDataActuatorMqttSubscribe():
...
    mqttclient.subscribe("IoT101/DeviceID/DataActuator", 0)
...
def functionDataSensorMqttPublish():
...
        topic = "IoT101/DeviceID/DataSensor"
... 
```

# 03 数据报告，系统通信协议，RESTFul API

章节 [系统通信协议](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/platform/Protocols.html) Flask-RESTful 实验室

**指导**

> 使用 Flask-RestFul 实现一个名为 "sensor" 的 RESTFul API，以发送从 functionDataSensor Python 函数下的模拟传感器获取的数据

实现后，运行你的 main.py 程序并使用 web 浏览器访问网络资源，你应该可以获取从模拟传感器获取的数据：

```
 root@edison:~/TheIoTLearningInitiative/InternetOfThings101# python main.py
     ...
     ...
     * Running on http://127.0.0.1:5000/ (Press CTRL+C to quit)
     * Restarting with stat
     * Debugger is active!
     * Debugger pin code: 331-202-890
     ...
     ... 
```

在 web 浏览器中连接到你的 boardipaddress:5000/sensor，数据将被显示

```
 127.0.0.1 - - [28/Dec/2015 15:07:38] "GET /sensor HTTP/1.1" 200 -
    127.0.0.1 - - [28/Dec/2015 15:07:40] "GET /sensor HTTP/1.1" 200 - 
```

# 04 数据报告，云计算服务，freeboard.io 和 dweet.io

章节 [云计算服务](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/platform/Services.html)

**指导**

> 创建一个 [freeboard.io](https://freeboard.io/) 仪表板，并使用 [dweet.io](http://dweet.io/) Python 库发送从模拟传感器获取的数据

不要犹豫去谷歌并查看这个链接 [BoardEdison en Freeboard con dweet](http://statusorel.ru/technology/boardedison-en-freeboard-con-dweet.html)

# 05 数据���告，云计算服务，adafruit.io

章节 [云计算服务](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/platform/Services.html)

**指导**

> 创建一个 [adafruit.Io](https://io.adafruit.com/) 仪表板，并使用 Adafruit MQTT Python 库发送从模拟传感器获取的数据

不要犹豫去谷歌并查看这个链接 [学习 Adafruit IO](https://learn.adafruit.com/adafruit-io/overview)

# 06 数据报告，云计算平台，IBM Watson IoT 平台

章节 [云计算平台](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/platform/Platforms.html)

**指导**

> 实现代码以将从模拟传感器获取的数据发布到 IBM Watson IoT 平台

记得重用在 "System Cloud Platforms IBM Watson IoT Platform Quickstart Physical Device" 下看到的代码，文件 [IBM IoT Quickstart](https://github.com/ibm-messaging/iot-gw-solutions/releases/download/1.03/ibm-iot-quickstart.zip)

# 07 物理传感器 Seeed Studio Grove Kit

**指导**

> 通过使用 Seeed Studio Grove Kit 中的物理执行器和传感器，实现代码以替换 functionDataActuator 和 functionDataSensor 下的现有功能/逻辑

需要更改 2 个函数中的代码：

+   functionDataActuator

+   functionDataSensor

记住 UPM 库为您提供了 Python 绑定，以便轻松使用您的 Grove 传感器

+   [`github.com/intel-iot-devkit/upm/tree/master/examples/python`](https://github.com/intel-iot-devkit/upm/tree/master/examples/python)

+   [传感器 Grove 光线](https://github.com/intel-iot-devkit/upm/blob/master/examples/python/grovelight.py)

+   [执行器 Grove 继电器](https://github.com/intel-iot-devkit/upm/blob/master/examples/python/groverelay.py)

这是新代码可能的样子：

```
#!/usr/bin/python

import paho.mqtt.client as paho
...
def functionDataActuator(status):
    # Implement logic to drive Actuator / Grove Relay
...
def functionDataSensor():
    # Use Sensor / Grove Light to replace psutil.net_io_counters()
    ...
    return data
... 
```

# 08 软件版本控制系统推送代码

章节 [软件版本控制系统](https://theiotlearninginitiative.gitbooks.io/internetofthings101/content/documentation/ControlVersionSystem.html)

**指导**

> 确认您本地 "TheIoTLearningInitiative" git 仓库中的每个代码，"InternetOfThings101" 目录已上传到您的远程 "TheIoTLearningInitiative" github 仓库

待办事项目录结构
