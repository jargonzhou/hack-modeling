"""
02. End-to-End Machine Learning Project
"""

from pathlib import Path
import tarfile
from typing import Any
import pandas as pd
import numpy as np
from zlib import crc32


def load_house_data(tarball_path: Path) -> pd.DataFrame:
  """load data"""
  with tarfile.open(tarball_path) as housing_tarball:
    housing_tarball.extractall(path=tarball_path.parent)
  return pd.read_csv(tarball_path.parent.joinpath("housing/housing.csv"))


def split_train_test(data: pd.DataFrame,
                     test_ratio: float,
                     random_state: int = 42) -> \
        tuple[pd.DataFrame, pd.DataFrame]:
  """split data to train set and test set"""
  np.random.seed(random_state)
  shuffled_indices = np.random.permutation(len(data))
  test_set_size = int(len(data) * test_ratio)
  test_indices = shuffled_indices[:test_set_size]
  train_indicies = shuffled_indices[test_set_size:]
  return data.iloc[train_indicies], data.iloc[test_indices]


def is_id_in_test_set(identifier: Any, test_ratio: float) -> bool:
  """return true when id is in test set"""
  return crc32(np.int64(identifier)) < test_ratio * 2 ** 32


def split_data_with_id_hash(data: pd.DataFrame,
                            test_ratio: float,
                            id_column: str) -> tuple[pd.DataFrame, pd.DataFrame]:
  """split data with id hash"""
  ids = data[id_column]
  in_test_set = ids.apply(lambda id_: is_id_in_test_set(id_, test_ratio))
  return data.loc[~in_test_set], data.loc[in_test_set]
