"""
Parsing utilities.
"""
from typing import Tuple
import numpy as np


def from_string(raw_str: str,
                dtype: np.typing.DTypeLike,
                count: int,
                result_shape: Tuple[int, ...],
                /,
                sep: str = ' ') -> np.ndarray:
  """
  construct from output of print(np.ndarray).

  https://stackoverflow.com/questions/38886641/convert-string-representation-of-array-to-numpy-array-in-python
  """
  raw_str = raw_str.replace('[', '').replace(']', '')
  return np.fromstring(string=raw_str, dtype=dtype, count=count, sep=sep).reshape(*result_shape)
