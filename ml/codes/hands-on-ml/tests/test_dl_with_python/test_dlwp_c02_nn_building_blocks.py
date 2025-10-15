"""2. The mathematical building blocks of neural networks

A first example of a neural network

tensors - a batch of data
- vector data: (samples, features)
- timeserias data, sequence data: (samples, timesteps, features)
- image: (samples, height, width, channels)
- video: (samples, frames, height, width, channels)

SGD

implement NN from scratch
"""

import unittest
import keras
from keras.datasets import mnist
from keras import layers, activations, optimizers, losses, metrics
import numpy as np
# import matplotlib.pyplot as plt
import tensorflow as tf


# pylint: skip-file


class TestFirstNNExample(unittest.TestCase):
  def setUp(self) -> None:
    (self.train_images, self.train_labels), \
        (self.test_images, self.test_labels) = mnist.load_data()
    self.assertTupleEqual((60000, 28, 28), self.train_images.shape)
    self.assertEqual(60000, len(self.train_labels))
    print(self.train_labels[0])
    self.assertTupleEqual((10000, 28, 28), self.test_images.shape)
    self.assertEqual(10000, len(self.test_labels))

    # preprocessing
    self.train_images = self.train_images.reshape((60000, 28 * 28))
    self.train_images = self.train_images.astype("float32") / 255
    self.test_images = self.test_images.reshape((10000, 28 * 28))
    self.test_images = self.test_images.astype("float32") / 255

  def test_mnist(self) -> None:
    # network architecture
    model = keras.Sequential([
        layers.Dense(512, activation=activations.relu),
        layers.Dense(10, activation=activations.softmax)
    ])

    # compile the model
    # model.compile(
    #     optimizer="adam",
    #     loss="sparse_categorical_crossentropy",
    #     metrics=["accuracy"],
    # )
    model.compile(optimizer=optimizers.Adam(),
                  loss=losses.sparse_categorical_crossentropy,
                  metrics=[metrics.sparse_categorical_accuracy],)

    # fitting the model
    model.fit(self.train_images, self.train_labels, epochs=5, batch_size=128)

    # make predictions
    test_digits = self.test_images[0:10]
    predictions = model.predict(test_digits)
    print(predictions[0])
    print(np.argmax(predictions[0]))
    print(self.test_labels[0])

    # evaluate the model
    test_loss, test_acc = model.evaluate(self.test_images, self.test_labels)
    print(f"test_loss={test_loss}, test_acc={test_acc}")
    # test_loss=0.05957219377160072, test_acc=0.9807999730110168


class TestTensor(unittest.TestCase):
  """data representation of NN: tensors

  tensor attributes:
  rank: number of axes
  shape
  data type(dtype)
  """

  def test_scalar(self) -> None:
    x = np.array(12)
    self.assertEqual(0, x.ndim)

  def test_vector(self) -> None:
    # 1 dimensional array: (n,)
    x = np.array([12, 3, 6, 14, 7])
    self.assertEqual(1, x.ndim)
    self.assertTupleEqual((5,), x.shape)

    # row vector: 1xn
    r = np.array([[12, 3, 6, 14, 7]])
    self.assertEqual(2, r.ndim)
    self.assertTupleEqual((1, 5), r.shape)

    # column vector: nx1
    c = np.array([[12], [3], [6], [14], [7]])
    self.assertEqual(2, c.ndim)
    self.assertTupleEqual((5, 1), c.shape)

    self.assertTrue(np.array_equal(r.reshape(-1, 1), c))  # row => column
    self.assertTrue(np.array_equal(r, c.reshape(1, -1)))  # column => row

  def test_matrix(self) -> None:
    x = np.array([[5, 78, 2, 34, 0],
                  [6, 79, 3, 35, 1],
                  [7, 80, 4, 36, 2]])
    self.assertEqual(2, x.ndim)

  def test_higher_rank_tensor(self) -> None:
    x = np.array([[[5, 78, 2, 34, 0],
                   [6, 79, 3, 35, 1],
                   [7, 80, 4, 36, 2]],
                  [[5, 78, 2, 34, 0],
                   [6, 79, 3, 35, 1],
                   [7, 80, 4, 36, 2]],
                  [[5, 78, 2, 34, 0],
                   [6, 79, 3, 35, 1],
                   [7, 80, 4, 36, 2]]])
    self.assertEqual(3, x.ndim)

  def test_tensor_attributes(self) -> None:
    (train_images, train_labels), \
        (test_images, test_labels) = mnist.load_data()
    self.assertEqual(3, train_images.ndim)
    self.assertTupleEqual((60000, 28, 28), train_images.shape)
    self.assertEqual(np.uint8, train_images.dtype)

    # plot digits
    # digit = train_images[4]
    # plt.imshow(digit, cmap=plt.cm.binary)
    # plt.title(f"label: {train_labels[4]}")
    # plt.show()

    # manipulate tensor with NumPy
    my_slice = train_images[10:100]
    self.assertTupleEqual((90, 28, 28), my_slice.shape)

    # data batches
    batch_size = 128
    n = 3
    batch = train_images[batch_size * n: batch_size * (n+1)]
    self.assertEqual(batch_size, len(batch))


class TestTensorOperation(unittest.TestCase):
  def test_element_wise_op(self) -> None:
    from dl_with_python.dlwp_c02_tensor import navie_relu, navie_add
    import time
    x = np.random.random((20, 100))
    y = np.random.random((20, 100))
    t0 = time.time()
    for _ in range(1000):
      z = x + y
      z = np.maximum(z, 0.)
    print(f"Took {time.time() - t0} s")  # Took 0.003002643585205078 s

    for _ in range(1000):
      z = navie_add(x, y)
      z = navie_relu(z)
    print(f"Took {time.time() - t0} s")  # Took 1.0450599193572998 s

  def test_broadcasting(self) -> None:
    X = np.random.random((32, 10))
    y = np.random.random((10,))

    # add axis
    y2 = np.expand_dims(y, axis=0)
    self.assertTupleEqual((1, 10), y2.shape)
    # repeat alongside the new axis
    y3 = np.concatenate([y2]*32, axis=0)
    self.assertTupleEqual((32, 10), y3.shape)

    from dl_with_python.dlwp_c02_tensor import navie_add_matrix_and_vector
    self.assertTrue(np.allclose(X+y3, navie_add_matrix_and_vector(X, y)))

    # (a,b,...,n,n+1,..., m), (n,n+1,...,m)
    x = np.random.random((64, 3, 32, 10))
    y = np.random.random((32, 10))
    z = np.maximum(x, y)
    self.assertTupleEqual((64, 3, 32, 10), z.shape)

  def test_tensor_product(self) -> None:
    """simulate np.dot()"""
    x = np.random.random((32,))  # means row vector: 1x32
    y = np.random.random((32,))
    z = np.dot(x, y)

    from dl_with_python.dlwp_c02_tensor import navie_vector_dot
    self.assertTrue(np.allclose(z, navie_vector_dot(x, y)))

    x = np.random.random((2, 32))
    y = np.random.random((32,))
    from dl_with_python.dlwp_c02_tensor import navie_matrix_vector_dot
    self.assertTrue(np.allclose(np.dot(x, y),
                    navie_matrix_vector_dot(x, y)))

    x = np.random.random((2, 32))
    y = np.random.random((32, 2))
    from dl_with_python.dlwp_c02_tensor import navie_matrix_dot
    self.assertTrue(np.allclose(np.dot(x, y),
                    navie_matrix_dot(x, y)))

  def test_tensor_reshape(self) -> None:
    x = np.array([[0., 1.],
                  [2., 3.],
                  [4., 5.]])
    self.assertTupleEqual((3, 2), x.shape)

    # reshape
    y = x.reshape((2, 3))
    self.assertTupleEqual((2, 3), y.shape)
    self.assertTrue(np.allclose(np.array([[0., 1., 2.], [3., 4., 5.]]), y))

    # transpose
    xt = np.transpose(x)
    self.assertTupleEqual((2, 3), xt.shape)
    self.assertTrue(np.allclose(np.array([[0., 2., 4.], [1., 3., 5.]]), xt))
    self.assertFalse(np.allclose(xt, y))

    z = x.reshape(3, 2)
    self.assertTrue(np.allclose(z, x))


class TestSGD(unittest.TestCase):
  """Graditent-based optimization"""

  def test_sgd(self):
    import tensorflow as tf
    # scalar
    x = tf.Variable(0.)
    with tf.GradientTape() as tape:
      y = 2 * x + 3
    grad_of_y_wrt_x = tape.gradient(y, x)
    self.assertIsInstance(grad_of_y_wrt_x, tf.Tensor)
    self.assertAlmostEqual(2.0, grad_of_y_wrt_x.numpy())

    # tensor
    x = tf.Variable(tf.random.uniform((2, 2)))
    with tf.GradientTape() as tape:
      y = 2 * x + 3
    grad_of_y_wrt_x = tape.gradient(y, x)
    self.assertIsInstance(grad_of_y_wrt_x, tf.Tensor)
    print(grad_of_y_wrt_x)

    # multiple variables
    W = tf.Variable(tf.random.uniform((2, 2)))
    b = tf.Variable(tf.zeros((2)))
    x = tf.random.uniform((2, 2))
    with tf.GradientTape() as tape:
      y = tf.matmul(W, x) + b
    grad_of_y_wrt_W_and_b = tape.gradient(y, [W, b])
    for t in grad_of_y_wrt_W_and_b:
      self.assertIsInstance(t, tf.Tensor)
      print(t)


class TestNNFromScratch(unittest.TestCase):

  def test_usage(self):
    from keras import ops
    from src.dl_with_python.dlwp_c02_nn_from_scratch import NavieDense, NavieSequential, fit
    model = NavieSequential([
        NavieDense(input_size=28*28, output_size=512, activation=tf.nn.relu),
        NavieDense(input_size=512, output_size=10, activation=tf.nn.softmax),
        # NavieDense(input_size=28*28, output_size=512, activation=ops.relu),
        # NavieDense(input_size=512, output_size=10, activation=ops.softmax),
    ])
    self.assertEqual(4, len(model.weights))

    (train_images, train_labels), \
        (test_images, test_labels) = mnist.load_data()
    # preprocessing
    train_images = train_images.reshape((60000, 28 * 28))
    train_images = train_images.astype("float32") / 255
    test_images = test_images.reshape((10000, 28 * 28))
    test_images = test_images.astype("float32") / 255

    fit(model, train_images, train_labels, epochs=10, batch_size=128)

    predictions = model(test_images[:10])
    predicted_labels = ops.argmax(predictions, axis=1)
    matches = predicted_labels == test_labels[:10]
    print(f"accuracy: {ops.mean(matches):.2f}")
    # accuracy: 0.90
