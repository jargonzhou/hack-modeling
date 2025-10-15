"""TensorFlow in Action
neural network computations
- matrix multiplication
- convolution operation
- pooling operation
"""

import unittest
import tensorflow as tf
import numpy as np

# pylint: skip-file


class TestNeuralNetworkComputation(unittest.TestCase):
  def test_PIL(self) -> None:
    from PIL import Image
    # Image.open(
    #     'data/tf_in_action/baboon.jpg').convert(mode='L').show()

    a = np.array(Image.open('data/tf_in_action/baboon.jpg'))
    print(a.shape, a.dtype)

  def test_ops(self) -> None:
    # 1. matrix_multiplication
    from PIL import Image
    x_rgb = np.array(Image.open(
        'data/tf_in_action/baboon.jpg')).astype('float32')
    self.assertTupleEqual((512, 512, 3), x_rgb.shape)
    x_rgb = tf.constant(x_rgb)

    grays = tf.constant([[299/1000], [587/1000], [114/1000]])
    self.assertListEqual([3, 1], grays.shape.as_list())

    x = tf.matmul(x_rgb, grays)
    x = tf.squeeze(x)
    self.assertListEqual([512, 512], x.shape.as_list())
    # https://pillow.readthedocs.io/en/stable/handbook/concepts.html
    Image.fromarray(x.numpy().astype('uint8'), mode='L') \
        .save('data/tf_in_action/baboon-gray.jpg')

    # 2. convolution operation
    y = tf.constant(x)
    # approximate Laplacian filter: edge detection filter
    filter = tf.Variable(np.array([[-1, -1, -1], [-1, 8, -1], [-1, -1, -1]])
                         .astype('float32'))
    y_reshaped = tf.reshape(y, [1, 512, 512, 1])
    filter_reshaped = tf.reshape(filter, [3, 3, 1, 1])
    y_conv = tf.nn.convolution(input=y_reshaped, filters=filter_reshaped)
    self.assertListEqual([1, 510, 510, 1],
                         y_conv.shape.as_list())
    y_conv2 = tf.squeeze(y_conv)
    Image.fromarray(y_conv2.numpy().astype('uint8'), mode='L') \
        .save('data/tf_in_action/baboon-gray-conv.jpg')

    # 3. pooling/sub-sampling operation
    z_avg = tf.nn.avg_pool(y_conv, ksize=(1, 2, 2, 1),
                           strides=(1, 2, 2, 1), padding='VALID')
    z_max = tf.nn.max_pool(y_conv, ksize=(1, 2, 2, 1),
                           strides=(1, 2, 2, 1), padding='VALID')
    z_avg = np.squeeze(z_avg.numpy())
    z_max = np.squeeze(z_max.numpy())
    Image.fromarray(z_avg.astype('uint8'), mode='L') \
        .save('data/tf_in_action/baboon-gray-pool-avg.jpg')
    Image.fromarray(z_max.astype('uint8'), mode='L') \
        .save('data/tf_in_action/baboon-gray-pool-max.jpg')
