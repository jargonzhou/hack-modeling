"""
Unit test of util.
"""

import unittest
import numpy as np

# pylint: skip-file


class TestUtil(unittest.TestCase):
  def test_dump_dir(self) -> None:
    from src.python_for_data_analysis.util.dump import dump_dir
    dump_dir(np)

  def test_from_string(self) -> None:
    from src.python_for_data_analysis.util.parse import from_string
    a = np.arange(24).reshape(4, 3, 2)
    aa = from_string(str(a), np.int32, 24, (4, 3, 2))
    np.testing.assert_array_equal(aa, a)

    a = a.reshape(2, 3, 4)
    aa = from_string(str(a), np.int16, 24, (2, 3, 4))
    np.testing.assert_array_equal(aa, a)
