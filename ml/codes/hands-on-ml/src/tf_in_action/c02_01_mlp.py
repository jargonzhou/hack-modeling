"""TensorFlow in Action
MLP: multilayer perceptron
"""

from collections.abc import Callable
import numpy as np
import tensorflow as tf


if __name__ == '__main__':
  x = np.random.normal(size=[1, 4]).astype('float32')

  init = tf.keras.initializers.RandomNormal()  # pylint: disable=no-member

  w1 = tf.Variable(init(shape=[4, 3]))
  b1 = tf.Variable(init(shape=[1, 3]))

  w2 = tf.Variable(init(shape=[3, 2]))
  b2 = tf.Variable(init(shape=[1, 2]))

  @tf.function
  def forward(x: tf.Tensor,  # pylint: disable=redefined-outer-name
              w: tf.Tensor, b: tf.Tensor, act: Callable[..., tf.Tensor]) -> tf.Tensor:
    """forward propagation"""
    return act(tf.matmul(x, w) + b)

  h = forward(x, w1, b1, tf.nn.sigmoid)
  y = forward(h, w2, b2, tf.nn.softmax)

  print(y)
