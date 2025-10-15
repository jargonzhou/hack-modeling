"""
Common utilities.
"""

import pandas as pd

import inspect
from types import ModuleType


def pd_print(obj):
  """pandas output"""
  if obj is None:
    return
  from IPython.core.display import display_html, HTML
  display_html(HTML(pd.json_normalize(obj).to_html()))


def inspect_submodules(module: ModuleType) -> None:
  """inspect submodules"""
  for k, m in inspect.getmembers(module,
                                 # and m.__name__.startswith(module.__name__)
                                 lambda m: inspect.ismodule(m)):
    if not k.startswith('_'):
      print(m.__name__)
      # inspect_classes(m)
      print()


def inspect_classes(module: ModuleType) -> None:
  """inspect classes in a module"""
  for k, c in inspect.getmembers(module,
                                 # and m.__module__.startswith(module.__name__)
                                 lambda m: inspect.isclass(m)):
    if not k.startswith('_'):
      print(c.__name__)


def inspect_functions(module: ModuleType) -> None:
  """inspect functions in a module"""
  for k, c in inspect.getmembers(module,
                                 lambda m: inspect.isfunction(m)):
    if not k.startswith('_'):
      print(c.__name__)
