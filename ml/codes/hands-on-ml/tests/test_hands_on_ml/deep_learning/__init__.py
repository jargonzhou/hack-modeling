"""
Part II. Neural Networks and Deep Learning
"""

from pathlib import Path
import os

# Keras HOME
os.environ['KERAS_HOME'] = Path.cwd().joinpath('data/keras').as_posix()
print(f"KERAS_HOME={os.environ['KERAS_HOME']}")

# path directory of models
_MODEL_DIR_PATH = Path.cwd().joinpath('data/hands_on_ml/models')
if not os.path.exists(_MODEL_DIR_PATH):
  print(f'create path: {_MODEL_DIR_PATH}')
  os.makedirs(_MODEL_DIR_PATH)

MODEL_PATH_DIR = _MODEL_DIR_PATH.as_posix()
