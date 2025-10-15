"""
JSON files.
"""

import json
import unittest
import pprint
from . import _DATA_DIR

# pylint: skip-file


class TestParseJSON(unittest.TestCase):
  def test_read(self) -> None:
    with open(_DATA_DIR + "/data-text.json") as f:
      data = json.loads(f.read())
      for item in data:
        pprint.pprint(item)
