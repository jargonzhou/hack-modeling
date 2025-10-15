"""
Unittest of 02. End-to-End Machine Learning Project
"""

import unittest
from tests.test_hands_on_ml import DATA_PATH

# pylint: skip-file


class TestEndToEndMLProject(unittest.TestCase):
  def test_load_house_data(self) -> None:
    from src.hands_on_ml.end_to_end_project import load_house_data
    df = load_house_data(tarball_path=DATA_PATH.joinpath("housing.tgz"))
    print(df.head())

  def setUp(self) -> None:
    from src.hands_on_ml.end_to_end_project import load_house_data
    self.df = load_house_data(tarball_path=DATA_PATH.joinpath("housing.tgz"))

  def test_split_train_test(self) -> None:
    from src.hands_on_ml.end_to_end_project import split_train_test
    train_set, test_set = split_train_test(
        self.df, test_ratio=0.2, random_state=42)
    print(len(train_set), len(test_set))

  def test_split_data_with_id_hash(self) -> None:
    from src.hands_on_ml.end_to_end_project import split_data_with_id_hash
    df_with_id = self.df.reset_index()  # add column 'index'
    train_set, test_set = split_data_with_id_hash(
        df_with_id, test_ratio=0.2, id_column='index')
    print(len(train_set), len(test_set))

    df_with_id['id'] = self.df["longitude"] * 1000 + self.df["latitude"]
    train_set, test_set = split_data_with_id_hash(
        df_with_id, test_ratio=0.2, id_column='id')
    print(len(train_set), len(test_set))
