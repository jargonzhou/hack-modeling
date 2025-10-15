"""TensorFlow in Action
TF building blocks
- tf.Varaible: shape, initial value, data type
  - tf.Variable(initial_value=None, trainable=None, dtype=None)
- tf.Tensor
- tf.Operation
"""

import unittest
import tensorflow as tf
import numpy as np

# pylint: skip-file


class TestTFBuildingBlocks(unittest.TestCase):
  def test_varibale(self) -> None:
    # tensor
    v1 = tf.Variable(tf.constant(2.0, shape=[4]), dtype='float32')
    print(v1)

    # Numpy ndarray
    v2 = tf.Variable(np.ones(shape=[4, 3]), dtype='float32')
    print(v2)

    # random initialization
    v3 = tf.Variable(tf.keras.initializers.RandomNormal()
                     (shape=[3, 4, 5]), dtype='float32')
    print(v3)

    # convert to NumPy ndarray
    arr = v1.numpy()
    self.assertIsInstance(arr, np.ndarray)

  def test_variable_assign(self) -> None:
    v = tf.Variable(np.zeros(shape=[4, 3]), dtype='float32')
    v = v[0, 2].assign(1)
    self.assertAlmostEqual(1, v.numpy()[0, 2])
    # slicing
    v = v[2:, :2].assign([[3, 3], [3, 3]])
    np.testing.assert_almost_equal(np.array([[3, 3], [3, 3]]),
                                   v[2:, :2].numpy())

  def test_tensor(self) -> None:
    v = tf.Variable(np.ones(shape=[4, 3]), dtype='float32')
    b = v * 3.0
    self.assertIsInstance(b, tf.Tensor)

    a = tf.constant(2, shape=[4], dtype='float32')
    b = tf.constant(3, shape=[4], dtype='float32')
    self.assertIsInstance(a, tf.Tensor)
    c = tf.add(a, b)
    self.assertIsInstance(c, tf.Tensor)

    # cannot assign
    with self.assertRaises(AttributeError) as cm:
      a = a[0].assign(2.0)
    self.assertEqual("'tensorflow.python.framework.ops.EagerTensor' object has no attribute 'assign'",
                     str(cm.exception))

  def test_tensor_type(self) -> None:
    print(tf.Tensor)
    # <class 'tensorflow.python.framework.tensor.Tensor'>

    # EagerTensor
    from tensorflow.python.framework.ops import EagerTensor
    print(EagerTensor)
    # <class 'tensorflow.python.framework.ops.EagerTensor'>
    self.assertTrue(issubclass(EagerTensor, tf.Tensor))

    from tensorflow.python.framework.composite_tensor import CompositeTensor

    # RaggedTensor
    self.assertTrue(issubclass(tf.RaggedTensor, CompositeTensor))

    # TensorArray
    print(tf.TensorArray)
    # <class 'tensorflow.python.ops.tensor_array_ops.TensorArray'>
    from tensorflow.python.ops.tensor_array_ops import TensorArray
    self.assertIs(tf.TensorArray, TensorArray)
    self.assertTrue(issubclass(TensorArray, object))

    # SparseTensor
    self.assertTrue(issubclass(tf.SparseTensor, CompositeTensor))

  def test_operation(self) -> None:
    a = tf.constant(4, shape=[4], dtype='float32')
    b = tf.constant(2, shape=[4], dtype='float32')
    # +
    c = a + b
    print(c)
    # tf.Tensor([6. 6. 6. 6.], shape=(4,), dtype=float32)
    # *
    e = a * b
    print(e)
    # tf.Tensor([8. 8. 8. 8.], shape=(4,), dtype=float32)
    # ==, <=
    equal_check = (a == b)
    print(equal_check)
    # tf.Tensor([False False False False], shape=(4,), dtype=bool)
    leq_check = (a <= b)
    print(leq_check)
    # tf.Tensor([False False False False], shape=(4,), dtype=bool)

  def test_operation_reduction(self) -> None:
    a = tf.constant(np.arange(5*4*3).reshape(5, 4, 3), dtype='int32')
    print(a)
    # reduce on all axes
    red_a1 = tf.reduce_sum(a)
    print(red_a1)
    # tf.Tensor(1770, shape=(), dtype=int32)

    # reduce on axis 0
    red_a2 = tf.reduce_prod(a, axis=0)
    print(red_a2)
    # tf.Tensor(
    # [[0   589225  1383200]
    # [2416635  3727360  5356445]
    # [7348320  9750895 12615680]
    # [15997905 19956640 24554915]], shape = (4, 3), dtype = int32)

    # reduce over multiple axes
    red_a3 = tf.reduce_min(a, axis=[0, 1])
    print(red_a3)
    # tf.Tensor([0 1 2], shape=(3,), dtype=int32)

    # keep dim
    red_a4 = tf.reduce_min(a, axis=1)
    self.assertListEqual([5, 3], red_a4.shape.as_list())
    red_a5 = tf.reduce_min(a, axis=1, keepdims=True)
    self.assertListEqual([5, 1, 3], red_a5.shape.as_list())

    # more
    # tf.argmax, tf.argmin, tf.cumsum
