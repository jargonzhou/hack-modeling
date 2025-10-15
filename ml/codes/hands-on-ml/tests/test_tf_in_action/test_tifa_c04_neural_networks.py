"""TensorFlow in Action
FCN: Fully connected networks
CNN: Convolutional neural networks 
RNN: Recurrent neural networks
"""

from typing import Any, override
import unittest
import numpy as np
import matplotlib.pyplot as plt
import tensorflow as tf
import pandas as pd

# pylint: skip-file


class TestFCN(unittest.TestCase):
  """sample FCN"""

  def generate_masked_inputs(self, x: np.ndarray, p: float, seed: float = None) -> np.ndarray:
    """gen masked inputs"""
    if seed:
      np.random.seed(seed)
    mask = np.random.binomial(n=1, p=p, size=x.shape).astype('float32')
    return x * mask

  def test_autoencoder(self) -> None:
    """sample autoencoder"""
    from keras.datasets.mnist import load_data as load_mnist_data
    from keras import layers, models
    from src.util.tf import plot_history

    # data
    (x_train, y_train), (x_test, y_test) = load_mnist_data()
    self.assertIsInstance(x_train, np.ndarray)
    self.assertIsInstance(y_train, np.ndarray)
    self.assertIsInstance(x_test, np.ndarray)
    self.assertIsInstance(y_test, np.ndarray)

    print('train shape', x_train.shape, y_train.shape)
    print('test shape', x_test.shape, y_test.shape)

    # data preprocessing
    norm_x_train = ((x_train - 128.0)/128.0).reshape(-1, 28*28)
    masked_x_train = self.generate_masked_inputs(norm_x_train, 0.5)

    # autoencoder
    autoencoder = models.Sequential([
        layers.Dense(64, activation='relu', input_shape=(28*28,)),
        layers.Dense(32, activation='relu'),
        layers.Dense(64, activation='relu'),
        layers.Dense(28*28, activation='tanh')
    ])
    autoencoder.compile(loss='mse', optimizer='adam')
    autoencoder.summary()
    # train model
    history = autoencoder.fit(
        masked_x_train, norm_x_train, batch_size=64, epochs=10)
    plot_history(history)
    # predicate
    x_train_sample = x_train[:10]
    # y_train_sample = y_train[:10]
    masked_x_train_sample = self.generate_masked_inputs(
        x_train_sample, 0.5, seed=42)
    norm_masked_x_train_sample = (
        (masked_x_train_sample-128.0)/128.0).reshape(-1, 28*28)
    y_pred = autoencoder.predict(norm_masked_x_train_sample)
    print('pred shape', y_pred.shape)

    # visualize result
    _f, axes = plt.subplots(2, 10, figsize=(18, 4))
    for i, (img, res) in enumerate(zip(masked_x_train_sample, y_pred)):
      r1, c1 = 0, i
      r2, c2 = 1, i
      axes[r1, c1].imshow(img, cmap='gray')
      axes[r1, c1].axis('off')

      res = ((res * 128.0)+128.0).reshape(28, 28)
      axes[r2, c2].imshow(res, cmap='gray')
      axes[r2, c2].axis('off')
    plt.show()


class TestCNN(unittest.TestCase):
  def format_data(self, x: tf.Tensor, depth: int):
    return (tf.cast(x['image'], 'float32'), tf.one_hot(x['label'], depth=depth))

  def test_cnn(self):
    import tensorflow_datasets as tfds
    from tests.test_tf_in_action import DEFAULT_DATA_DIR
    from keras.models import Sequential
    from keras.layers import Conv2D, MaxPool2D, Flatten, Dense
    import keras.backend as K
    from src.util.tf import plot_history
    # data
    ds, ds_info = tfds.load(name='cifar10',
                            data_dir=DEFAULT_DATA_DIR,
                            with_info=True)
    print(ds, ds_info)
    # Split('train'): <_PrefetchDataset element_spec={
    #   'id': TensorSpec(shape=(), dtype=tf.string, name=None),
    #   'image': TensorSpec(shape=(32, 32, 3), dtype=tf.uint8, name=None),
    #   'label': TensorSpec(shape=(), dtype=tf.int64, name=None)}>

    train_data = ds['train'].map(
        lambda x: self.format_data(x, depth=10)).batch(32)

    # model
    K.clear_session()
    cnn = Sequential(layers=[
        Conv2D(filters=16, kernel_size=(3, 3), strides=(2, 2),
               activation='relu', padding='same', input_shape=(32, 32, 3)),
        MaxPool2D(pool_size=(2, 2), strides=(2, 2), padding='same'),
        Conv2D(filters=32, kernel_size=(3, 3),
               activation='relu', padding='same'),
        MaxPool2D(pool_size=(2, 2), strides=(2, 2), padding='same'),
        Flatten(),
        Dense(64, activation='relu'),
        Dense(10, activation='softmax')
    ])
    cnn.summary()
    # train model
    cnn.compile(loss='categorical_crossentropy',
                optimizer='adam', metrics=['acc'])
    history = cnn.fit(train_data, epochs=25)
    # history = cnn.fit(train_data.take(10), epochs=5) # test
    plot_history(history)

    # predicate
    test_data: tf.data.Dataset = ds['train']
    test_data_10 = test_data.shuffle(100, seed=4321).take(10)
    test_data_t = test_data_10.map(
        lambda x: self.format_data(x, depth=10)).batch(32)
    labels_pred = cnn.predict(test_data_t, batch_size=16)
    # Take 10 samples randomly to plot
    sample_images, sample_labels = [], []
    for d in test_data_10:
      sample_images.append(d["image"].numpy())
      sample_labels.append(d["label"].numpy())
    # Creating a label map mapping the integer label to the string
    label_map = dict(zip(
        list(range(10)),
        ["airplane", "automobile", "bird", "cat", "deer", "dog", "frog", "horse", "ship", "truck"]))
    # Plotting the images
    _, axes = plt.subplots(2, 5, figsize=(9, 4))
    for i, (img, lbl) in enumerate(zip(sample_images, sample_labels)):
      r, c = i//5, i % 5
      axes[r, c].imshow(img, cmap='gray')
      axes[r, c].axis('off')
      label_pred = label_map[np.argmax(labels_pred[i])]
      np.int64(7)
      axes[r, c].set_title(
          "Label: {}\npred: {}".format(label_map[lbl], label_pred))
    plt.show()


class TestRNN(unittest.TestCase):
  @override
  def setUp(self):
    import os
    import requests
    self.data_path = 'data/tf_in_action/co2-mm-gl.csv'
    if not os.path.exists(self.data_path):
      print(f'not found {self.data_path}, download...')
      url = "https://datahub.io/core/co2-ppm/r/co2-mm-gl.csv"
      r = requests.get(url)
      with open(self.data_path, 'wb') as f:
        f.write(r.content)
    self.data = pd.read_csv(self.data_path)
    self.assertIsNotNone(self.data)
    print(self.data.info())
    print(self.data.head())

  def gen_data(self, co2_arr: pd.Series, n_seq: int) -> tuple[np.ndarray, np.ndarray]:
    x, y = [], []
    for i in range(co2_arr.shape[0] - n_seq):
      x.append(co2_arr[i:i+n_seq-1])
      y.append(co2_arr[i+n_seq-1:i+n_seq])
    x = np.array(x).reshape(-1, n_seq-1, 1)
    y = np.array(y)
    print(f'shape of x,y: {x.shape} {y.shape}')
    # shape of x,y: (544, 12, 1) (544, 1)
    return x, y

  def test_co2(self):
    from keras.layers import SimpleRNN, Dense
    from keras.models import Sequential
    from src.util.tf import plot_history

    self.data = self.data.set_index('Date')
    # print(self.data.head())
    # self.data[['Average']].plot(figsize=(12, 6))
    # plt.show()

    # preprocessing
    self.data["Average Diff"] = self.data["Average"] - \
        self.data["Average"].shift(1).fillna(method='bfill')
    # self.data['Average Diff'].plot(figsize=(12, 6))
    # plt.show()

    # model
    rnn = Sequential([
        SimpleRNN(64),
        Dense(64, activation='relu'),
        Dense(1)
    ])
    rnn.compile(loss='mse', optimizer='adam')
    rnn.summary()

    x, y = self.gen_data(self.data['Average Diff'], n_seq=13)
    train_history = rnn.fit(x, y, shuffle=True, batch_size=64, epochs=25)
    plot_history(train_history)

    # predicate
    history = self.data['Average Diff'].values[-12:].reshape(1, -1, 1)
    true_values = []
    prev_true_value = self.data['Average'].values[-1]
    for i in range(60):
      p_diff = rnn.predict(history).reshape(1, -1, 1)
      history = np.concatenate((history[:, 1:, :], p_diff), axis=1)
      true_values.append(prev_true_value+p_diff[0, 0, 0])
      prev_true_value = true_values[-1]
    # Plotting the current and predicted trends
    plt.figure(figsize=(16, 6))
    # Plotting the current trend
    plt.plot(self.data["Average"], c='r',
             linestyle='--', label="Current trend")
    # Creating a pd.Series from predictions
    pred_ser = pd.Series(
        [self.data["Average"].values[-1]]+true_values,
        index=[self.data.index[-1]]+[
            pd.to_datetime(self.data.index[-1], format="%Y-%m") +
            pd.DateOffset(months=i+1)
            for i in range(60)]
    )
    pred_ser.index = pd.to_datetime(pred_ser.index).strftime('%Y-%m')
    # Plotting the predictions
    plt.plot(pred_ser, c='g', label='Predicted trend')
    # Annotating the plot
    plt.xticks(np.arange(0, self.data["Average"].shape[0]+60, 24), rotation=45)
    plt.xlabel('Time', fontsize=18)
    plt.ylabel('CO2 Concentration', fontsize=18)
    plt.legend(prop={'size': 15})
    plt.title('Evolution of CO2 Concentration over Time', fontsize=18)
    plt.show()
