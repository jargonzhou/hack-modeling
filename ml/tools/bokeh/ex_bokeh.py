from bokeh.models import CustomJS, Slider, ColumnDataSource
from bokeh.plotting import curdoc
from bokeh.layouts import column, row
from bokeh.plotting import figure
from numpy.random import random

################################################################################
# Creating a single slider application
################################################################################


def example1():
  slider = Slider(start=0, end=10, value=1, step=.1, title="Stuff")
  slider.js_on_change("value", CustomJS(code="""
      console.log('slider: value=' + this.value, this.toString())
  """))
  return row(slider)

################################################################################
# Create multiple slider widgets
################################################################################


def example2():
  slider_widget1 = Slider(start=0, end=100, step=10, value=0, title='Slider 1')
  slider_widget2 = Slider(start=0, end=50, step=5, value=0, title='Slider 2')
  slider_widget3 = Slider(start=50, end=100, step=5, value=0, title='Slider 3')

  for w in (slider_widget1, slider_widget2, slider_widget3):
    w.js_on_change("value", CustomJS(code="""
      console.log('slider: value=' + this.value, this.toString())
    """))
  return column(slider_widget1, slider_widget2, slider_widget3)

################################################################################
# Combining the slider application with a scatter plot
################################################################################


def example3():
  # Create data for the plot
  initial_points = 500
  data_points = ColumnDataSource(data={'x': random(initial_points),
                                       'y': random(initial_points)})
  # Create the plot
  plot = figure(title="Random scatter plot generator")
  plot.diamond(x='x', y='y', source=data_points, color='red')
  # Create the slider widget
  slider_widget = Slider(start=0, end=10000, step=10, value=initial_points,
                         title='Slide right to increase number of points')

  def callback(attr, old, new):  # Define the callback function
    points = slider_widget.value
    data_points.data = {'x': random(points), 'y': random(points)}

  slider_widget.on_change('value', callback)
  return column(slider_widget, plot)

################################################################################
# Combining the slider application with a line plot
################################################################################


def example4():
  # Define the points that create the line plot
  x = [1, 2, 3, 4, 5, 6, 7, 8, 9]
  y = [2, 3, 4, 5, 6, 7, 8, 9, 10]
  # Create the data source
  data_points = ColumnDataSource(data={'x': x, 'y': y})
  # Create the line plot
  plot = figure(title='Random Line plot generator')
  plot.line('x', 'y', source=data_points, color='red')
  # Create the slider widget
  slider_widget = Slider(start=0, end=100, step=1, value=10)
  # Define the callback function

  def callback(attr, old, new):
    points = slider_widget.value
    data_points.data = {'x': random(points), 'y': random(points)}
  slider_widget.on_change('value', callback)

  return row(slider_widget, plot)

################################################################################
# Creating an application with the select widget
################################################################################


def example5():
  from bokeh.models import Select
  from numpy.random import random, normal
  # Create data for the plot
  initial_points = 500
  data_points = ColumnDataSource(data={'x': random(initial_points),
                                       'y': random(initial_points)})
  # Create the plot
  plot = figure(title="Scatter plot distribution selector")
  plot.scatter(x='x', y='y', marker='diamond', source=data_points, color='red')
  # Create the select widget
  select_widget = Select(options=['uniform distribution', 'normal distribution'],
                         value='uniform distribution', title='Select the distribution of your choice')

  def callback(attr, old, new):  # Define the callback function
    if select_widget.value == 'uniform distribution':
      function = random
    else:
      function = normal
    data_points.data = {'x': function(size=initial_points),
                        'y': function(size=initial_points)}

  select_widget.on_change('value', callback)
  # Create a layout for the application
  return row(select_widget, plot)

################################################################################
# Creating an application with the button widget
################################################################################


def example6():
  from bokeh.models import Button
  import numpy as np
  # Create data for the plot
  initial_points = 500
  data_points = ColumnDataSource(data={'x': random(initial_points),
                                       'y': random(initial_points)})
  # Create the plot
  plot = figure(title="Data change application")
  plot.diamond(x='x', y='y', source=data_points, color='red')
  # Create the button widget
  button_widget = Button(label='Change Data')
  # Define the callback function

  def callback():
    # New y values
    y = np.cos(initial_points) + random(initial_points)
    data_points.data = {'x': random(initial_points), 'y': y}
  button_widget.on_click(callback)
  # Create a layout for the application
  return row(button_widget, plot)

################################################################################
# Creating an application to select different columns
################################################################################


def example7():
  import pandas as pd
  from bokeh.models import Select
  # Read in the data
  df = pd.read_csv(
      '../dataset/cache/datasets/camnugent/sandp500/versions/4/all_stocks_5yr.csv')
  # Filtering for apple stocks
  df_apple = df[df['Name'] == 'AAL']
  # Create the ColumnDataSource object
  data = ColumnDataSource(data={
      'x': df_apple['high'],
      'y': df_apple['low'],
      'x1': df_apple['volume']
  })
  # Creating the scatter plot
  plot = figure(title='Attribute selector application')
  plot.diamond('x', 'y', source=data, color='red')
  # Creating the select widget
  select_widget = Select(options=['low', 'volume'],
                         value='low',
                         title='Select a new y axis attribute')
  # Define the callback function

  def callback(attr, old, new):
    if new == 'low':
      data.data = {'x': df_apple['high'], 'y': df_apple['low']}
    else:
      data.data = {'x': df_apple['high'], 'y': df_apple['volume']}
  select_widget.on_change('value', callback)
  # Add the layout to the application
  return row(select_widget, plot)
################################################################################
# layout
################################################################################

# slider_layout = column(slider)


################################################################################
# Add the layout to the application
################################################################################
curdoc().add_root(example7())
