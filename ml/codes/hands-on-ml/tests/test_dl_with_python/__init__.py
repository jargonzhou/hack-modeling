"""Deep Learning with Python
"""

from pathlib import Path
import os

# Keras HOME
os.environ['KERAS_HOME'] = Path.cwd().joinpath('data/keras').as_posix()
print(f"KERAS_HOME={os.environ['KERAS_HOME']}")
