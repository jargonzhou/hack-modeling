"""
CSV file.
"""

import csv
import pprint
import unittest
from csv import DictReader
from csv import writer
from . import _DATA_DIR

# pylint: skip-file


class TestParseCSV(unittest.TestCase):
  def test_load(self) -> None:
    with open(_DATA_DIR + '/data-text.csv', 'rt') as f:
      reader = csv.reader(f)
      for row in reader:
        print(row)

  def test_DictReader(self) -> None:
    with open(_DATA_DIR + '/data-text.csv', 'rt') as f:
      header_rdr = DictReader(f)
      header_rows = [h for h in header_rdr]
      pprint.pprint(header_rows)

  def test_write(self) -> None:
    data_file = _DATA_DIR + '/data-text-output.csv'
    with open(data_file, 'wt') as f:
      csv_writer = writer(f, lineterminator='\n')
      title = ['C1', 'C2', 'C3']
      csv_writer.writerow(title)
      data = [('11', '12', '13'), ('21', '22', '12'),]
      csv_writer.writerows(data)

    # cleanup
    import os
    os.remove(data_file)
