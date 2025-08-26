"""
Dump utilities.
"""

from typing import Any
from collections.abc import Callable
import numpy as np


def dump_dir(m: Any, /, f: Callable[[str], bool] | None = None) -> None:
  """output dir(m)"""
  for idx, s in enumerate(dir(m)):
    if f is None or f(s):
      if idx > 0 and idx % 10 == 0:
        print(f"{s}", end="\n")
      else:
        print(s, end=" ")


def dump_ndarray(a: np.typing.NDArray) -> None:
  """output properties in ndarray."""
  ndarray_dump_str = f"""type: {type(a)}
flags: {a.flags}
shape: {a.shape}
strides: {a.strides}
ndim: {a.ndim}
data: {a.data}
size: {a.size}
itemsize: {a.itemsize}
nbytes: {a.nbytes}
base: {a.base}
dtype:
  type: {a.dtype.type}
  char: {a.dtype.char}
  str: {a.dtype.str}
  names: {a.dtype.names}
"""
  print(ndarray_dump_str)
