"""
Utilities for TF.

see also
- keras.utils.plot_model
"""

from pathlib import Path
from time import strftime

import matplotlib.pyplot as plt
from keras.callbacks import History


def plot_history(history: History) -> None:
  """plot history of model.fit()"""

  for key in history.history.keys():
    plt.plot(history.epoch, history.history[key], label=key)
  plt.xlabel('Epoch')
  plt.legend()
  plt.show()


def get_run_logdir(root_logdir: str = 'data/tf_logs') -> Path:
  """create run log dir named with datetime"""
  return Path(root_logdir) / strftime("run_%Y_%m_%d_%H_%M_%S")
