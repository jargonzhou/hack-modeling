"""
Examining the TensorFlow Graph
https://www.tensorflow.org/tensorboard/graphs
"""

import unittest
from keras.models import Sequential
from keras.layers import Flatten, Dense, Dropout, Input
from keras.datasets.fashion_mnist import load_data
from keras.callbacks import TensorBoard

from src.util.tf import get_run_logdir

# pylint: skip-file


class TestTensorBoard(unittest.TestCase):
  def test_model_graph(self):
    # Define the model.
    model = Sequential([
        Input(shape=(28, 28)),
        Flatten(),
        Dense(32, activation='relu'),
        Dropout(0.2),
        Dense(10, activation='softmax')
    ])

    model.compile(
        optimizer='adam',
        loss='sparse_categorical_crossentropy',
        metrics=['accuracy'])

    (train_images, train_labels), _ = load_data()
    train_images = train_images / 255.0

    tensorboard_callback = TensorBoard(log_dir=get_run_logdir(),
                                       write_graph=True,
                                       profile_batch=(100, 200))

    # Train the model.
    model.fit(
        train_images,
        train_labels,
        batch_size=64,
        epochs=5,
        callbacks=[tensorboard_callback])
