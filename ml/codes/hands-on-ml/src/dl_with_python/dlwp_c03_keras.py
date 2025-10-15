"""
core Keras API
"""

from typing import override
from keras import layers, initializers, ops


class SimpleDense(layers.Layer):  # pylint: disable=abstract-method
  """simple dense layer"""

  def __init__(self, units: int, activation=None):
    super().__init__()
    self.units = units  # number of hidden units in the layer
    self.activation = activation

  @override
  def build(self, input_shape):
    """create weights"""
    input_dim = input_shape[-1]  # last dimension
    self.W = self.add_weight(shape=(input_dim, self.units),  # pylint: disable=invalid-name,attribute-defined-outside-init
                             initializer=initializers.random_normal)
    self.b = self.add_weight(  # pylint: disable=attribute-defined-outside-init
        shape=(self.units,), initializer=initializers.zeros)

  @override
  def call(self, inputs):  # pylint: disable=arguments-differ
    """forward pass"""
    y = ops.matmul(inputs, self.W) + self.b
    if self.activation is not None:
      y = self.activation(y)
    return y
