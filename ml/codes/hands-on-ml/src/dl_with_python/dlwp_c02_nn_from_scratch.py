"""
NN workflow implementation.
"""

import math
# import keras
import tensorflow as tf
# from keras import ops
from keras import losses


class NavieDense:
  """output = activation(dot(W, input) + b)"""

  def __init__(self, input_size: int, output_size: int, activation):
    self.activation = activation
    # W
    w_shape = (input_size, output_size)
    w_initial_value = tf.random.uniform(w_shape, minval=0, maxval=1e-1)
    self.W = tf.Variable(w_initial_value)  # pylint: disable=invalid-name
    # self.W = keras.Variable(
    #     shape=(input_size, output_size), initializer="uniform")
    # b
    b_shape = (output_size,)
    b_initial_value = tf.zeros(b_shape)
    self.b = tf.Variable(b_initial_value)
    # self.b = keras.Variable(shape=(output_size,), initializer="zeros")

  def __call__(self, inputs):
    return self.activation(tf.matmul(inputs, self.W) + self.b)
    # return self.activation(ops.matmul(inputs, self.W) + self.b)

  @property
  def weights(self) -> list[tf.Variable]:
    """weights: [W, b]"""
    return [self.W, self.b]


class NavieSequential:
  """sequential architecture"""

  def __init__(self, layers: list[NavieDense]):
    self.layers = layers

  def __call__(self, inputs):
    x = inputs
    for layer in self.layers:
      x = layer(x)
    return x

  @property
  def weights(self) -> list[tf.Variable]:
    """weights of model"""
    weights = []
    for layer in self.layers:
      weights += layer.weights
    return weights


class BatchGenerator:
  """generate data batch"""

  def __init__(self, images, labels, batch_size=128):
    assert len(images) == len(labels)
    self.index = 0
    self.images = images
    self.labels = labels
    self.batch_size = batch_size
    self.mun_batches = math.ceil(len(images) / batch_size)

  def next(self):
    """get next batch of data"""
    images = self.images[self.index:self.index + self.batch_size]
    labels = self.labels[self.index:self.index + self.batch_size]
    self.index += self.batch_size
    return images, labels


def one_train_step(model: NavieSequential, images_batch, labels_batch):
  """one step training step"""
  with tf.GradientTape() as tape:
    predictions = model(images_batch)
    loss = losses.sparse_categorical_crossentropy(labels_batch, predictions)
    # loss = ops.sparse_categorical_crossentropy(labels_batch, predictions)
    avg_loss = tf.reduce_mean(loss)
    # avg_loss = ops.mean(loss)
  gradients = tape.gradient(avg_loss, model.weights)
  # print(gradients)
  update_weights(gradients, model.weights)
  return avg_loss


learning_rate = 1e-3


def update_weights(gradients: list[tf.Tensor], weights: list[tf.Variable]):
  """use gradient to update weights"""
  for g, w in zip(gradients, weights):
    w.assign_sub(g * learning_rate)
  # optimizer = optimizers.SGD(learning_rate=learning_rate)
  # optimizer.apply_gradients(zip(gradients, weights))


def fit(model: NavieSequential, images, labels, epochs: int, batch_size: int = 128):
  """fitting model"""
  for epoch in range(epochs):
    print(f"Epoch {epoch}")
    # batches in epoch
    batch_gen = BatchGenerator(images, labels, batch_size)
    for batch in range(batch_gen.mun_batches):
      images_batch, labels_batch = batch_gen.next()
      loss = one_train_step(model, images_batch, labels_batch)
      if batch % 100 == 0:
        print(f"loss at batch {batch}: {loss:.2f}")
