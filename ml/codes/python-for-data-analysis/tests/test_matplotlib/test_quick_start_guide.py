"""
Quick start guide: https://matplotlib.org/stable/users/explain/quick_start.html
"""

import matplotlib.pyplot as plt
import unittest

# pylint: skip-file


class TestQuickStartGuide(unittest.TestCase):
  def test_typing(self) -> None:
    from matplotlib.axes import Axes, Subplot
    from matplotlib.figure import Figure
    from matplotlib.lines import Line2D
    from matplotlib.axis import Axis, Tick, XAxis, YAxis
    from matplotlib.ticker import Locator, Formatter

    # Create a figure containing a single Axes.
    fig, ax = plt.subplots()
    self.assertIsInstance(fig, Figure)
    self.assertIsInstance(ax, Axes)

    # Plot some data on the Axes.
    plot_res = ax.plot([1, 2, 3, 4], [1, 4, 2, 3])
    self.assertIsInstance(plot_res, list)
    self.assertTrue(len(plot_res) > 0)
    self.assertIsInstance(plot_res[0], Line2D)

    # Show the figure.
    plt.show()
