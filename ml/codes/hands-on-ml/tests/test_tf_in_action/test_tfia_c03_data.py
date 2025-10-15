"""TensorFlow in Action
retrieve data
- tf.data API
- Keras data generator
- tensorflow-datasets
"""

import tensorflow as tf
import unittest
import os

# pylint: skip-file


class TestTFData(unittest.TestCase):
  def get_image(self, file_path):
    img = tf.io.read_file(file_path)
    img = tf.image.decode_png(img, channels=3)
    img = tf.image.convert_image_dtype(img, tf.float32)
    return tf.image.resize(img, [64, 64])

  def test_tf_data(self):
    # dataset: https://www.kaggle.com/datasets/olgabelitskaya/flower-color-images/data
    data_dir = os.path.join('data/tf_in_action', 'flower_images') + os.path.sep
    csv_ds = tf.data.experimental.CsvDataset(
        os.path.join(data_dir, 'flower_labels.csv'),
        record_defaults=("", -1),
        header=True)
    for item in csv_ds.take(5):
      print(item)

    fname_ds = csv_ds.map(lambda a, b: a)
    label_ds = csv_ds.map(lambda a, b: b)
    image_ds = fname_ds.map(
        lambda p: self.get_image(data_dir + p))

    label_ds = label_ds.map(lambda x: tf.one_hot(x, depth=10))
    data_ds = tf.data.Dataset.zip((image_ds, label_ds))
    # shuffle
    data_ds = data_ds.shuffle(buffer_size=20)
    # batch
    data_ds = data_ds.batch(5)
    for item in data_ds.take(1):
      print(item)
      self.assertListEqual([5, 64, 64, 3], item[0].shape.as_list())
      self.assertListEqual([5, 10], item[1].shape.as_list())

    # model
    from keras.layers import Conv2D, Flatten, Dense
    from keras.models import Sequential
    model = Sequential([
        Conv2D(64, (5, 5), activation='relu', input_shape=(64, 64, 3)),
        Flatten(),
        Dense(10, activation='softmax')
    ])
    model.compile(loss='categorical_crossentropy',
                  optimizer='adam', metrics=['acc'])
    model.summary()

    history = model.fit(data_ds, epochs=10)
    from src.util.tf import plot_history
    plot_history(history)


class TestKerasData(unittest.TestCase):
  def test_image_data_gen(self):
    import tensorflow.keras as tfkeras

    data_dir = os.path.join('data/tf_in_action', 'flower_images')
    # class ImageDataGenerator: DEPRECATED.
    # https://www.tensorflow.org/api_docs/python/tf/keras/preprocessing/image
    img_gen = tfkeras.preprocessing.image.ImageDataGenerator()

  def test_mnist(self):
    from keras.datasets.mnist import load_data
    # default download to ~/.keras/datasets, use env KERAS_HOME to override
    (x_train, y_train), (x_test, y_test) = load_data()
    self.assertTupleEqual((60000, 28, 28), x_train.shape)
    self.assertTupleEqual((10000, 28, 28), x_test.shape)
    self.assertTupleEqual((60000,), y_train.shape)
    self.assertTupleEqual((10000,), y_test.shape)

    # more: https://keras.io/api/datasets/


class TestTFDatasets(unittest.TestCase):
  def test_load(self):
    import tensorflow_datasets as tfds
    from . import DEFAULT_DATA_DIR
    # print(tfds.list_builders())
    # print()
    # print(tfds.list_dataset_collections())

    # https://www.tensorflow.org/datasets/api_docs/python/tfds/load
    # example dataset: https://www.tensorflow.org/datasets/catalog/aeslc
    # fix NonMatchingChecksumError
    # .venv\Lib\site-packages\tensorflow_datasets\datasets\aeslc\checksums.tsv
    # default download to ~/tensorflow_datasets, use data_dir to override
    ds, ds_info = tfds.load('aeslc', data_dir=DEFAULT_DATA_DIR, with_info=True)
    print(ds.keys())
    # dict_keys(['train', 'validation', 'test'])
    self.assertIsInstance(ds['train'], tf.data.Dataset)
    self.assertIsInstance(ds_info, tfds.core.DatasetInfo)
    print(ds)
    print()
    print(ds_info)
