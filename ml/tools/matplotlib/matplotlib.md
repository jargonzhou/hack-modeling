# Matplotlib
* http://matplotlib.org/
  * [Plot types](https://matplotlib.org/stable/plot_types/index)
  * [Examples](https://matplotlib.org/stable/gallery/index.html)
  * [API Reference](https://matplotlib.org/stable/api/index.html)
  * [Matplotlib cheatsheets and handouts](https://matplotlib.org/cheatsheets/)
* https://github.com/matplotlib/matplotlib

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

books:
* Gaël Varoquaux et al. [Scientific Python Lectures](https://lectures.scientific-python.org/)-
* Python for Data Analysis: Data Wrangling with pandas, NumPy & Jupyter, 2022

# Concepts

* `Figure`: 图, 整个用户界面窗口 ![anatomy of a figure](https://matplotlib.org/stable/_images/anatomy.png)
  * subplots: 网格状的子图
  * `Axes`: 附加到图的artist, 包含一个区域用于数据制图, 通常包含axis以提供数据范围. 有titile, x-label, y-label.
  * `Axis`: 设置范围和限制, 生成tick和ticklabel
  * `Artist`: 图中可见的部分, 包括`Figure`, `Axes`, `Axis`, `Text`, `Line2D`, `collections`, `Patch`等.
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
import matplotlib as mpl
import matplotlib.pyplot as plt

# Jupyter notebook
%matplotlib inline
%matplotlib notebook
```

## API
* https://matplotlib.org/stable/api/index.html

```python
Figure
Axes
  plot()
plt
  subplots() -> tuple[Figure, Axes]
  show()
```

Subplots
```python
# init figure
plt.figure() -> Figure
plt.gcf() -> Figure # get current figure

# init subplot as axes
plt.subplot() -> Axes

# add subplot
Figure.add_subplot() -> Axes

# init an array of subplots
plt.subplots() -> tuple[Figure, Axes]
  sharex, sharey

# align subplots of different dimensions
plt.subplot2grid(shape, loc, rowspan, colspan) -> Axes

# inset plots
Figure.add_axes(rect) -> Axes

# adjust subplot dimensions post hoc
plt.subplots_adjust(left, right, top, bottom)

# set margin
plt.tight_layout() # pad, w_pad, h_pad
```

Axes
```python
Axes.xaxis.set_major_locator()
Axes.yaxis.set_minor_formatter()

plt.xscale()      # before Axes defined
Axes.set_xscale() # after Axes defined
```

## Coding styles
- OO-style: explicitly create `Figure` and `Axes`, call methods of them.
- pyplot-style: implicitly create `Figure` and `Axes`, use pyplot functions for plotting.
- helper functions

> see [matplotlib.ipynb](./matplotlib.ipynb)

# Types of Plots
* https://matplotlib.org/stable/plot_types/index.html

* 线图或标记: `plt.plot()`
* 散点图: `plt.scatter()`
* 条形图: `plt.bar()`
* 等值线图: `plt.contour()`
* 图片: `plt.imshow()`
* 箭头图: `plt.quiver()`
* 饼图: `plt.pie()`
* 网格: `plt.grid()`
* 极坐标: `plt.polar()`
* 多个图: `plt.subplot()`
* 文本: `plt.text()`
* 3D

## Plot Styles

* `Axes.plot()`
  - https://matplotlib.org/stable/api/_as_gen/matplotlib.axes.Axes.plot.html
* `pyplot.plot()`
  - https://matplotlib.org/stable/api/_as_gen/matplotlib.pyplot.plot.html
* color
  - https://matplotlib.org/stable/gallery/color/color_demo.html
  - colormap: https://matplotlib.org/stable/gallery/color/colormap_reference.html
* marker: denote data point
  - https://matplotlib.org/stable/gallery/lines_bars_and_markers/marker_reference.html
  - style: shape, size, color
* line: `Line2D`
  - https://matplotlib.org/stable/gallery/lines_bars_and_markers/linestyles.html
  - cap stype: https://matplotlib.org/stable/gallery/lines_bars_and_markers/capstyle.html
  - style: color, thickness, dash pattern, dash cap
* spine
  - https://matplotlib.org/stable/gallery/spines/index.html
* text, labels, annotations
  - https://matplotlib.org/stable/gallery/text_labels_and_annotations/index.html
  - arrow: https://matplotlib.org/stable/gallery/text_labels_and_annotations/fancyarrow_demo.html

# Customize Matplotlib
* https://matplotlib.org/stable/users/explain/customizing.html

- runtime rc(runtime configuration) settings
```python
print(matplotlib.rcParams)

# set rcParams
mpl.rcParams['lines.linewidth'] = 2
mpl.rcParams['lines.linestyle'] = '--'
plt.plot(data)

# use rc()
mpl.rc('lines', linewidth=4, linestyle='-.')
plt.plot(data)

# Temporary rc settings
with mpl.rc_context({'lines.linewidth': 2, 'lines.linestyle': ':'}):
    plt.plot(data)
```
- style sheets
```python
print(plt.style.available)
plt.style.use('ggplot')
```
- `matplotlibrc` file
```
print(matplotlib.matplotlib_fname())
```

# Backends
* https://matplotlib.org/stable/users/explain/figure/backends.html

# `animation`
* https://matplotlib.org/stable/users/explain/animations/index.html
* https://matplotlib.org/stable/gallery/animation/index.html

More:
- PyGame
- FFmpeg
- avconv
- mencoder
- Pillow
- ImageMagick

# `widgets`
* https://matplotlib.org/stable/gallery/widgets/index.html

# Toolkit
* https://matplotlib.org/stable/users/explain/toolkits/index.html

- axisartist: The axisartist contains a custom Axes class that is meant to support curvilinear grids (e.g., the world coordinate system in astronomy).
- axes_grid1
- mplot3d: Generating 3D plots using the mplot3d toolkit.

# Map
* https://github.com/matplotlib/basemap

# See Also

* [Bokeh](../bokeh/bokeh.md): Interactive Data Visualization in the browser, from Python.
* [GeoPandas](https://github.com/geopandas/geopandas): Python tools for geographic data.
* [mpld3](https://github.com/mpld3/mpld3): A D3 Viewer for Matplotlib.
* [mplfinance](https://github.com/matplotlib/mplfinance): matplotlib utilities for the visualization, and visual analysis, of financial data.
* [pandas `DataFrame.plot()`](https://pandas.pydata.org/docs/reference/api/pandas.DataFrame.plot.html)
* [Plotly](https://plotly.com/python/): Plotly's Python graphing library makes interactive, publication-quality graphs. Examples of how to make line plots, scatter plots, area charts, bar charts, error bars, box plots, histograms, heatmaps, subplots, multiple-axes, polar charts, and bubble charts.
* [pyecharts](https://github.com/pyecharts/pyecharts): Apache ECharts 是一个由百度开源的数据可视化，凭借着良好的交互性，精巧的图表设计，得到了众多开发者的认可。而 Python 是一门富有表达力的语言，很适合用于数据处理。当数据分析遇上数据可视化时，pyecharts 诞生了。
* [seaborn](./seaborn.md): statistical data visualization.
* [Vega-Altair](https://altair-viz.github.io/): Vega-Altair is a declarative visualization library for Python. Its simple, friendly and consistent API, built on top of the powerful Vega-Lite grammar, empowers you to spend less time writing code and more time exploring your data.
