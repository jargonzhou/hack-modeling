# Matplotlib
* http://matplotlib.org/
  * [Plot types](https://matplotlib.org/stable/plot_types/index)
  * [Examples](https://matplotlib.org/stable/gallery/index.html)
  * [API Reference](https://matplotlib.org/stable/api/index.html)
  * [Matplotlib cheatsheets and handouts](https://matplotlib.org/cheatsheets/)
* [Code](https://github.com/matplotlib/matplotlib)
* Gaël Varoquaux et al. [Scientific Python Lectures](https://lectures.scientific-python.org/)

> Matplotlib: Visualization with Python
>
> Matplotlib is a comprehensive library for creating static, animated, and interactive visualizations in Python. Matplotlib makes easy things easy and hard things possible.
> 
> The project was started by John Hunter in 2002 to enable a MATLAB-like plotting interface in Python.
>
> * Create [publication quality plots](https://ieeexplore.ieee.org/document/4160265/citations?tabFilter=papers).
> * Make [interactive figures](https://mybinder.org/v2/gh/matplotlib/mpl-brochure-binder/main?labpath=MatplotlibExample.ipynb) that can zoom, pan, update.
> * Customize [visual style|https://matplotlib.org/stable/gallery/style_sheets/style_sheets_reference.html]] and [[layout](https://matplotlib.org/stable/tutorials/provisional/mosaic.html).
> * Export to [many file formats](https://matplotlib.org/stable/api/figure_api.html#matplotlib.figure.Figure.savefig).
> * Embed in [JupyterLab and Graphical User Interfaces](https://matplotlib.org/stable/gallery/#embedding-matplotlib-in-graphical-user-interfaces).
> * Use a rich array of [third-party packages](https://matplotlib.org/mpl-third-party/) built on Matplotlib.



# Terminology

* figure: 图, 整个用户界面窗口
  * subplots: 网格状的子图
  * axes: 轴, 与子图类似, 但可以在图中任意位置
* spines: 脊柱, 连接轴刻度标记的线, 标识数据区域边界.
  * ticks: 刻度
  * major tick: 主刻度
  * minor tick: 次刻度
  * major tick label: 主刻度标签
  * minor tick label: 次刻度标签
  * tick locator: 刻度定位器 `NullLocator`, `MultipleLocator`, `FixedLocator`, `IndexLocator`, `LinearLocator`, `LogLocator`, `AutoLocator`.
* title: 标题
* X axis label: X轴标签
* Y axis label: Y轴标签
* grid: 网格
* line plot(Line): 线图
* scatter plot(markers): 散点图
* legend: 图例
* colormaps: 色彩图


# Usage

```python
%matplotlib inline

import matplotlib.pyplot as plt
```

## Types of Plots

* 线图或标记: `plt.plot()`
* 散点图: `plt.scatter()`
* 条形图: `plt.bar()`
* 等值线图: `plt.contour()`
* 图片: `plt.imshow()`
* 箭头图: `plt.quiver()`
* 饼图: `plt.pie()`
* 网格: `plt.grid()`
* 极坐标
* 多个图: `plt.subplot()`
* 文本: `plt.text()`
* 3D

## `matplotlibrc`

file path in miniconda: `D:\software\miniconda3\pkgs\matplotlib-base-3.9.2-py312h90004f6_2\Lib\site-packages\matplotlib\mpl-data\matplotlibrc`.

# See Also

* [seaborn](./seaborn.md)
* [Vega-Altair](https://altair-viz.github.io/): Vega-Altair is a declarative visualization library for Python. Its simple, friendly and consistent API, built on top of the powerful Vega-Lite grammar, empowers you to spend less time writing code and more time exploring your data.
* [Bokeh](https://docs.bokeh.org/en/latest/): Bokeh is a Python library for creating interactive visualizations for modern web browsers. It helps you build beautiful graphics, ranging from simple plots to complex dashboards with streaming datasets. With Bokeh, you can create JavaScript-powered visualizations without writing any JavaScript yourself.
* [Plotly](https://plotly.com/python/): Plotly's Python graphing library makes interactive, publication-quality graphs. Examples of how to make line plots, scatter plots, area charts, bar charts, error bars, box plots, histograms, heatmaps, subplots, multiple-axes, polar charts, and bubble charts.



