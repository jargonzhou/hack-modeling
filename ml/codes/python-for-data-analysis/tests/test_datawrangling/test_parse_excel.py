"""
Excel files.
"""
import unittest

import xlrd
from . import _DATA_DIR
# pylint: skip-file


class TestParseExcel(unittest.TestCase):
  # v2.0.0 Remove support for anything other than .xls files.
  # https://xlrd.readthedocs.io/en/latest/changes.html
  def test_read(self) -> None:
    book = xlrd.open_workbook(
        _DATA_DIR + "/SOWC 2014 Stat Tables_Table 9.xls")

    for sheet in book.sheets():
      print(sheet.name)

    sheet = book.sheet_by_name("Table 9 ")
    print(sheet)

    for i in range(sheet.nrows):
      row = sheet.row_values(i)
      for cell in row:
        print(cell)
