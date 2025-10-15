# Bokeh
* https://docs.bokeh.org/en/latest/
* https://github.com/bokeh/bokeh


> Bokeh is a Python library for creating interactive visualizations for modern web browsers. It helps you build beautiful graphics, ranging from simple plots to complex dashboards with streaming datasets. With Bokeh, you can create JavaScript-powered visualizations without writing any JavaScript yourself.

actions:
- [bokeh.ipynb](./bokeh.ipynb)
- `python-for-data-analysis/tests/test_bokeh/test_first_step.py`

# Scenarios
* Applications: Build Powerful Data Applications
![](http://bokeh.org/img/apps.gif)
* Dashboards: Publish Sophisticated Dashboards
![](http://bokeh.org/img/dashboard.png)
* Exploration: Interactively Explore Data in Notebooks
![](http://bokeh.org/img/eda.gif)
* Streaming: Visualize Streaming Data
![](http://bokeh.org/img/streaming.gif)
* Website: Add Content to Web Pages
![](http://bokeh.org/img/web.png)


# Concepts
* application: a rendered Bokeh document runs in the browser
* glyphs: building block of Bokeh, including lines, circles, rectangles and other shapes
* server: share and publish interactive plots and apps
* widgets: sliders, drop-down menus and other tools that embed in plot to add some interactivity

# Widgets
* https://docs.bokeh.org/en/latest/docs/user_guide/interaction/widgets.html

# Server
* https://docs.bokeh.org/en/latest/docs/user_guide/server.html

## FAQ
* [How to stop bokeh from opening a new tab in Jupyter Notebook?](https://stackoverflow.com/questions/51512907/how-to-stop-bokeh-from-opening-a-new-tab-in-jupyter-notebook): `bokeh.io.reset_output()`