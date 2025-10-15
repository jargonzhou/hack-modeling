"""
PDF files.

slate: online parse
pdfminer: tool convert pdf to text
pdftables
"""

import slate3k

import unittest
from . import _DATA_DIR

# pylint: skip-file


class TestParsePDF(unittest.TestCase):
  def test_read(self) -> None:
    with open(_DATA_DIR + "/EN-FINAL Table 9.pdf", 'rb') as f:
      doc = slate3k.PDF(f)

      for page in doc:
        print(page)
