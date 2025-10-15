"""3. Introduction to Keras and TensorFlow

train a nn:
low-level tensor manipulation
- tensors: include variables to store network state
- tensor operations: add, relu, matmul
- backprogapation: compute the gradient of math expressions
high-level deep learning concepts
- layers: form models
- loss function: define the feedback signal used for learning
- optimizer: determine how learning proceeds
- metrics: evaluate model performance
- training loop: perform minibatch sgd

TensorFlow

Keras
"""

import unittest
import tensorflow as tf
import keras
import numpy as np

# pylint: skip-file


class TestTensorFlow(unittest.TestCase):
  def test_tensors(self):
    # constant
    x = tf.constant([[1.0, 2.0], [3.0, 4.0]])
    self.assertIsInstance(x, tf.Tensor)
    self.assertListEqual([2, 2], x.shape.as_list())  # shape
    self.assertEqual(tf.float32, x.dtype)  # dtype
    self.assertEqual(np.float32, x.dtype.as_numpy_dtype)
    self.assertIsInstance(x.numpy(), np.ndarray)  # as NumPy array
    # ones, zeros
    x = tf.ones(shape=(2, 1))
    self.assertIsInstance(x, tf.Tensor)
    x = tf.zeros(shape=(2, 1))
    self.assertIsInstance(x, tf.Tensor)
    # random tensors
    x = tf.random.normal(shape=(3, 1), mean=0., stddev=1.)
    self.assertIsInstance(x, tf.Tensor)
    x = tf.random.uniform(shape=(3, 1), minval=0., maxval=1.)
    self.assertIsInstance(x, tf.Tensor)
    # NOT assignable
    with self.assertRaises(TypeError) as cm:
      x = tf.ones(shape=(2, 2))
      x[0, 0] = 0.
    self.assertEqual("'tensorflow.python.framework.ops.EagerTensor' object does not support item assignment",
                     str(cm.exception))

    # variable
    v = tf.Variable(initial_value=tf.random.normal(shape=(3, 1)))
    self.assertIsInstance(v, tf.Variable)
    self.assertNotIsInstance(v, tf.Tensor)
    print(v)
    v.assign(tf.ones((3, 1)))  # assignment
    print(v)
    v.assign_add(tf.ones((3, 1)))
    self.assertIsInstance(v[0, 0], tf.Tensor)
    v[0, 0].assign(3.)

  def test_tensor_operation(self):
    a = tf.ones((2, 2))
    b = tf.square(a)
    c = tf.sqrt(a)
    d = b + c
    e = tf.matmul(a, b)
    e *= d
    print(e)

  def test_graditent_tape(self):
    input_var = tf.Variable(initial_value=3.)
    with tf.GradientTape() as tape:
      result = tf.square(input_var)  # y = x^2
    gradient = tape.gradient(result, input_var)
    print(gradient)
    self.assertIsInstance(gradient, tf.Tensor)
    self.assertAlmostEqual(6.0, gradient.numpy())  # scalar value

    input_const = tf.constant(3.)
    with tf.GradientTape() as tape2:
      # by default, only trainable variables are tracked
      tape2.watch(input_const)
      result2 = tf.square(input_const)  # y = c^2
    gradient = tape2.gradient(result2, input_const)
    print(gradient)
    self.assertIsInstance(gradient, tf.Tensor)
    self.assertAlmostEqual(6.0, gradient.numpy())

    # second-order gradient
    time = tf.Variable(0.)
    with tf.GradientTape() as outer_tape:
      with tf.GradientTape() as inner_tape:
        position = 4.9 * time ** 2
      speed = inner_tape.gradient(position, time)
    acceleration = outer_tape.gradient(speed, time)
    print(acceleration)
    self.assertAlmostEqual(9.8, acceleration.numpy())

  # end to end example: see dlwp_c03.ipynb


class TestKeras(unittest.TestCase):
  def test_layers(self):
    from src.dl_with_python.dlwp_c03_keras import SimpleDense
    from keras import ops, Sequential
    dense = SimpleDense(units=32, activation=ops.relu)
    input = tf.ones(shape=(2, 28*28))
    output = dense(input)
    print(output)
    self.assertListEqual([2, 32], output.shape.as_list())

    model = Sequential([
        SimpleDense(32, activation=ops.relu),
        SimpleDense(64, activation=ops.relu),
        SimpleDense(32, activation=ops.relu),
        SimpleDense(10, activation=ops.softmax)])
    input = tf.ones(shape=(2, 28*28))
    output = model(input)
    print(output)
    self.assertListEqual([2, 10], output.shape.as_list())

  # anatomy of a neural network: see dlwp_c03.ipynb
