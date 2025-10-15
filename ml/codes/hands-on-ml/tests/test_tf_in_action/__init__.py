"""
Unittest of TF.
"""

from pathlib import Path
import os

# TF data_dir
DEFAULT_DATA_DIR: str = Path.cwd().joinpath('data/tf').as_posix()
print(f'TF data_dir={DEFAULT_DATA_DIR}')

# Keras HOME
os.environ['KERAS_HOME'] = Path.cwd().joinpath('data/keras').as_posix()
print(f"KERAS_HOME={os.environ['KERAS_HOME']}")

os.environ["KERAS_BACKEND"] = "tensorflow"
print(f"KERAS_BACKEND={os.environ['KERAS_BACKEND']}")
