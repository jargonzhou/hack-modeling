# R
* https://www.r-project.org/
  * [Books related to R](https://www.r-project.org/doc/bib/R-books.html)
  * [The R Manuals](https://cran.r-project.org/manuals.html)
    * An Introduction to R
    * R Data Import/Export
    * R Installation and Administration	
    * Writing R Extensions
    * A draft of The R language definition
    * R Internals
    * The R Reference Index

books:
* R in a Nutshell
* R Cookbook
* Graphing Data with R
* R for Data Science
* An Introduction to Statistical Learning: with Applications in R

## Introduction to R

R is a language and environment for statistical computing and graphics. It is a GNU project which is similar to the S language and environment which was developed at Bell Laboratories (formerly AT&T, now Lucent Technologies) by John Chambers and colleagues. R can be considered as a different implementation of S. There are some important differences, but much code written for S runs unaltered under R.

R provides a wide variety of statistical (linear and nonlinear modelling, classical statistical tests, time-series analysis, classification, clustering, …) and graphical techniques, and is highly extensible. The S language is often the vehicle of choice for research in statistical methodology, and R provides an Open Source route to participation in that activity.

One of R’s strengths is the ease with which well-designed publication-quality plots can be produced, including mathematical symbols and formulae where needed. Great care has been taken over the defaults for the minor design choices in graphics, but the user retains full control.

R is available as Free Software under the terms of the Free Software Foundation’s GNU General Public License in source code form. It compiles and runs on a wide variety of UNIX platforms and similar systems (including FreeBSD and Linux), Windows and MacOS.

! Terminology

* CRAN: The ''C''omprehensive ''R'' ''A''rchive ''N''etwork

! <<a "Packages">> 包

* [Available CRAN Packages By Name](https://cran.r-project.org/web/packages/available_packages_by_name.html)
* [Quick list of useful R packages](https://support.posit.co/hc/en-us/articles/201057987-Quick-list-of-useful-R-packages) - 2024-04-26

|包名                    |说明                                                                                                                  |
|:---|:---|
|assertthat              |Easy Pre and Post Assertions                                                                                          |
|base                    |The R Base Package<br>R语言基础函数, 包括算术运算、I/O、编程支持等函数.                                               |
|base64enc               |Tools for base64 encoding                                                                                             |
|boot                    |Bootstrap Functions (Originally by Angelo Canty for S)<br>自助重复抽样.                                               |
|class                   |Functions for Classification<br>分类算法, 包括最近邻、自组织映射、学习矢量量化等算法.                                 |
|cli                     |Helpers for Developing Command Line Interfaces                                                                        |
|cluster                 |"Finding Groups in Data": Cluster Analysis Extended Rousseeuw et al.<br>聚类算法.                                     |
|codetools               |Code Analysis Tools for R<br>分析R代码的工具.                                                                         |
|compiler                |The R Compiler Package<br>R编译器.                                                                                    |
|crayon                  |Colored Terminal Output                                                                                               |
|datasets                |The R Datasets Package<br>一些著名的数据集.                                                                           |
|digest                  |Create Compact Hash Digests of R Objects                                                                              |
|ellipsis                |Tools for Working with ...                                                                                            |
|evaluate                |Parsing and Evaluation Tools that Provide More Details than the Default                                               |
|fansi                   |ANSI Control Sequence Aware String Functions                                                                          |
|foreign                 |Read Data Stored by 'Minitab', 'S', 'SAS', 'SPSS', 'Stata', 'Systat', 'Weka', 'dBase', ...<br>读取其它格式数据的工具. |
|glue                    |Interpreted String Literals                                                                                           |
|graphics                |The R Graphics Package<br>基本绘图函数.                                                                               |
|grDevices               |The R Graphics Devices and Support for Colours and Fonts<br>支持base和grid绘图的绘图设备, 包括系统支持工具.           |
|grid                    |The Grid Graphics Package<br>比base包更精细的绘图工具.                                                                |
|htmltools               |Tools for HTML                                                                                                        |
|IRdisplay               |'Jupyter' Display Machinery                                                                                           |
|IRkernel                |Native R Kernel for the 'Jupyter Notebook'                                                                            |
|jsonlite                |A Robust, High Performance JSON Parser and Generator for R                                                            |
|KernSmooth              |Functions for Kernel Smoothing Supporting Wand & Jones (1995)                                                         |
|lattice                 |Trellis Graphics for R<br>R中的栅格图, 比默认效果更美观.                                                              |
|lifecycle               |Manage the Life Cycle of your Package Functions                                                                       |
|MASS                    |Support Functions and Datasets for Venables and Ripley's MASS<br>Modern Applied Statistics with S中的函数和数据.      |
|Matrix                  |Sparse and Dense Matrix Classes and Methods                                                                           |
|methods                 |Formal Methods and Classes<br>S4中引入的标准方法和类的实现.                                                           |
|mgcv                    |Mixed GAM Computation Vehicle with Automatic Smoothness Estimation<br>广义可加模型和广义可加混合模型.                 |
|nlme                    |Linear and Nonlinear Mixed Effects Models<br>线性和非线性混合效应模型.                                                |
|nnet                    |Feed-Forward Neural Networks and Multinomial Log-Linear Models<br>前馈神经网络和多项对数线性模型.                     |
|nutshell                |Data for "R in a Nutshell"                                                                                            |
|nutshell.audioscrobbler |Audioscrobbler data for "R in a Nutshell"                                                                             |
|nutshell.bbdb           |Baseball Database for "R in a Nutshell"                                                                               |
|parallel                |Support for Parallel computation in R<br>支持并行计算, 包括随机数生成.                                                |
|pbdZMQ                  |Programming with Big Data -- Interface to 'ZeroMQ'                                                                    |
|pillar                  |Coloured Formatting for Columns                                                                                       |
|repr                    |Serializable Representations                                                                                          |
|rlang                   |Functions for Base Types and Core R and 'Tidyverse' Features                                                          |
|rpart                   |Recursive Partitioning and Regression Trees<br>建立递归的分类和回归树模型的工具.                                      |
|spatial                 |Functions for Kriging and Point Pattern Analysis<br>实现Kriging插值法和点模式分析的函数.                              |
|splines                 |Regression Spline Functions and Classes<br>回归样条函数和类.                                                          |
|stats                   |The R Stats Package<br>用于统计计算与随机数生成的函数, 包括常用的统计检验、概率分布和建模工具.                        |
|stats4                  |Statistical Functions using S4 Classes<br>S4的统计函数.                                                               |
|survival                |Survival Analysis<br>生存分析函数.                                                                                    |
|tcltk                   |Tcl/Tk Interface<br>Tcl/Tk接口, 用于创建平台无关的UI工具.                                                             |
|tools                   |Tools for Package Development<br>开发R包的工具.                                                                       |
|utf8                    |Unicode Text Processing                                                                                               |
|utils                   |The R Utils Package<br>R的一系列使用功能, 包括包管理、文件的读写和编辑.                                               |
|uuid                    |Tools for Generating and Handling of UUIDs                                                                            |
|vctrs                   |Vector Helpers                                                                                                        |


# Applications

* [CRAN Task View: Time Series Analysis](https://cran.r-project.org/web/views/TimeSeries.html)