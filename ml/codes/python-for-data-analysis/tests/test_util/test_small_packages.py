"""
Small utility packages.
"""

import unittest


# pylint: skip-file


class TestSmallPackages(unittest.TestCase):
  def test_treelib(self) -> None:
    # An efficient implementation of tree data structure in pure python.
    # https://github.com/caesar0301/treelib
    from treelib import Tree
    tree = Tree()
    tree.create_node("Harry", "harry")  # root node
    tree.create_node("Jane", "jane", parent="harry")
    tree.create_node("Bill", "bill", parent="harry")
    tree.create_node("Diane", "diane", parent="jane")
    tree.create_node("Mary", "mary", parent="diane")
    tree.create_node("Mark", "mark", parent="jane")
    tree.show()

  def test_prettytable(self) -> None:
    # A simple Python library for easily displaying tabular data in a visually appealing ASCII table format
    # https://pypi.org/project/prettytable/
    from prettytable import PrettyTable

    # Row by row
    table = PrettyTable()
    table.field_names = ["City name", "Area", "Population", "Annual Rainfall"]
    table.add_row(["Adelaide", 1295, 1158259, 600.5])
    table.add_row(["Brisbane", 5905, 1857594, 1146.4])
    table.add_row(["Darwin", 112, 120900, 1714.7])
    table.add_row(["Hobart", 1357, 205556, 619.5])
    table.add_row(["Sydney", 2058, 4336374, 1214.8])
    table.add_row(["Melbourne", 1566, 3806092, 646.9])
    table.add_row(["Perth", 5386, 1554769, 869.4])
    print(table)

    # All rows at once
    table = PrettyTable()
    table.field_names = ["City name", "Area", "Population", "Annual Rainfall"]
    table.add_rows([
        ["Adelaide", 1295, 1158259, 600.5],
        ["Brisbane", 5905, 1857594, 1146.4],
        ["Darwin", 112, 120900, 1714.7],
        ["Hobart", 1357, 205556, 619.5],
        ["Sydney", 2058, 4336374, 1214.8],
        ["Melbourne", 1566, 3806092, 646.9],
        ["Perth", 5386, 1554769, 869.4],
    ])
    print(table)

    # Column by column
    table = PrettyTable()
    table.add_column("City name",
                     ["Adelaide", "Brisbane", "Darwin", "Hobart", "Sydney", "Melbourne", "Perth"])
    table.add_column("Area",
                     [1295, 5905, 112, 1357, 2058, 1566, 5386])
    table.add_column("Population",
                     [1158259, 1857594, 120900, 205556, 4336374, 3806092,  1554769])
    table.add_column("Annual Rainfall",
                     [600.5, 1146.4, 1714.7, 619.5, 1214.8, 646.9, 869.4])
    # alignment: l, r, c
    table.align = "l"
    print(table)
