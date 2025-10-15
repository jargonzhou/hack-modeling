"""
10. Introduction to Artificial Neural Networks with Keras


see also:
- test_tfia_c03_keras.py
"""

import unittest
import numpy as np
import tensorflow as tf
from keras.models import Sequential, load_model
from keras.layers import Flatten, Dense, Normalization
from keras.activations import relu, softmax
from keras.losses import sparse_categorical_crossentropy
from keras.optimizers import SGD
from keras.metrics import sparse_categorical_accuracy
from keras.callbacks import TensorBoard

from src.util.tf import plot_history, get_run_logdir
from . import MODEL_PATH_DIR

# pylint: skip-file


class TestMLPWithKeras(unittest.TestCase):
  def setUp(self):
    # log dir
    self.run_logdir = get_run_logdir()
    # data
    from keras.datasets.fashion_mnist import load_data
    self.fashion_mnist = load_data()
    (x_train_full, y_train_full), (self.X_test, self.y_test) = self.fashion_mnist
    self.X_train, self.y_train = x_train_full[:-5000], y_train_full[:-5000]
    self.X_valid, self.y_valid = x_train_full[-5000:], y_train_full[-5000:]
    print('X_train', self.X_train.shape, self.X_train.dtype)
    print('y_train', self.y_train.shape, self.y_train.dtype)
    # data preprocessing
    self.X_train, self.X_valid, self.X_test = self.X_train / \
        255., self.X_valid / 255., self.X_test / 255.
    # class names
    self.class_names = ["T-shirt/top", "Trouser", "Pullover", "Dress", "Coat",
                        "Sandal", "Shirt", "Sneaker", "Bag", "Ankle boot"]

  def test_sequential_api_for_classifer(self):
    # create model
    tf.random.set_seed(42)
    model = Sequential([
        Flatten(input_shape=[28, 28]),
        Dense(300, activation=relu),
        Dense(100, activation=relu),
        Dense(10, activation=softmax)
    ])

    model.summary()

    for layer in model.layers:
      print(layer)
      from keras.layers import Layer
      self.assertIsInstance(layer, Layer)
    hidden1 = model.layers[1]  # dense layer
    weights, biases = hidden1.get_weights()
    print(
        f'layer 0 weights shape={weights.shape}, biases shape={biases.shape}')

    # compile model
    model.compile(loss=sparse_categorical_crossentropy,
                  optimizer=SGD(),
                  metrics=[sparse_categorical_accuracy])

    # train model
    n_epochs = 5
    # callbacks
    tensorboard_cb = TensorBoard(self.run_logdir
                                 #  , profile_batch=(100, 200)
                                 )
    history = model.fit(self.X_train, self.y_train,
                        epochs=n_epochs,
                        callbacks=[tensorboard_cb],
                        validation_data=(self.X_valid, self.y_valid))
    plot_history(history)

    # evaluate model
    print('metric names:', model.metrics_names)
    # metric names: ['loss', 'compile_metrics']
    print(model.evaluate(self.X_test, self.y_test))

    # predict
    n_new = 3
    X_new = self.X_test[:n_new]
    print('actual:', np.array(self.class_names)[self.y_test[:n_new]])
    # actual: ['Ankle boot' 'Pullover' 'Trouser']
    y_proba = model.predict(X_new)
    y_pred = y_proba.argmax(axis=-1)
    print('pred:', np.array(self.class_names)[y_pred])
    # pred: ['Ankle boot' 'Pullover' 'Trouser']

    # save model: suffix .keras, .h5
    model_path = MODEL_PATH_DIR + '/my_keras_model.keras'
    model.save(model_path)

    # load model
    saved_model = load_model(model_path)
    y_proba = saved_model.predict(X_new)
    y_pred = y_proba.argmax(axis=-1)
    print('pred:', np.array(self.class_names)[y_pred])
    # pred: ['Ankle boot' 'Pullover' 'Trouser']

  def test_sequential_api_for_regression(self):
    pass

  def test_functional_api(self):
    pass

  def test_subclassing_api(self):
    pass

  def test_tensorboard_summary(self):
    """tf.summary"""
    test_logdir = get_run_logdir()
    writer = tf.summary.create_file_writer(str(test_logdir))
    with writer.as_default():
      for step in range(1, 1000+1):
        tf.summary.scalar("my_scalar", np.sin(step / 10), step=step)

        data = (np.random.randn(100)+1) * step / 100
        tf.summary.histogram("my_hist", data, buckets=50, step=step)

        images = np.random.rand(2, 32, 32, 3) * step / 1000
        tf.summary.image("my_images", images, step=step)

        texts = ["The step is " + str(step), "Its square is " + str(step ** 2)]
        tf.summary.text("my_text", texts, step=step)

        sine_wave = tf.math.sin(tf.range(12000) / 48000 * 2 * np.pi * step)
        audio = tf.reshape(tf.cast(sine_wave, tf.float32), [1, -1, 1])
        tf.summary.audio("my_audio", audio, sample_rate=48000, step=step)
