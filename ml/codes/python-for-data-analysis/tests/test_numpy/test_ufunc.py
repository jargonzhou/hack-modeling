"""
Unit test of NumPy ufuncs(universal functions).
"""

import unittest
import numpy as np

# pylint: skip-file


class TestUfucs(unittest.TestCase):
  def test_frompyfunc(self) -> None:
    # https://numpy.org/doc/stable/reference/generated/numpy.frompyfunc.html#numpy-frompyfunc
    # add broadcasting to oct
    oct_array = np.frompyfunc(oct, 1, 1)
    a = oct_array(np.array((10, 30, 100)))
    print(a, a.dtype)
    # ['0o12' '0o36' '0o144'] object
    b = np.array((oct(10), oct(30), oct(100)))
    print(b, b.dtype)
    # ['0o12' '0o36' '0o144'] <U5
    np.testing.assert_array_equal(a, b)

  def test_methods(self) -> None:
    # ufunc methods: reduce, accumulate, reduceat, outer, at
    x = np.arange(9).reshape(3, 3)
    print(x)
    # [[0 1 2]
    #  [3 4 5]
    #  [6 7 8]]
    print(np.add.reduce(x, 1))
    # [ 3 12 21]
    print(np.add.reduce(x, (0, 1)))
    # 36


class TestElementwiseOp(unittest.TestCase):

  # math operations

  def test_scalar(self) -> None:
    a = np.array([1, 2, 3, 4])
    print(a, a + 1, 2 ** a)
    # [1 2 3 4] [2 3 4 5] [ 2  4  8 16]

  def test_arith(self) -> None:
    a = np.array([1, 2, 3, 4])
    b = np.ones(4) + 1
    print(a, b)
    # [1 2 3 4] [2. 2. 2. 2.]
    print(a - b, a * b)
    # [-1.  0.  1.  2.] [2. 4. 6. 8.]

    j = np.arange(5)
    print(j, 2 ** (j+1) - j)
    # [0 1 2 3 4] [ 2  3  6 13 28]

  def test_compare(self) -> None:
    a = np.array([1, 2, 3, 4])
    b = np.array([4, 2, 2, 4])
    print(a == b, a > b)
    # [False  True False  True] [False False  True False]

  # trigonometric functions

  def test_trig(sef) -> None:
    a = np.arange(5)
    print(np.sin(a), np.log(a), np.exp(a))
    # [ 0.          0.84147098  0.90929743  0.14112001 -0.7568025 ] [      -inf 0.         0.69314718 1.09861229 1.38629436] [ 1.          2.71828183  7.3890561  20.08553692 54.59815003]

  # bit-twiddling functions

  # comparsion functions

  def test_compare_array(self) -> None:
    a = np.array([1, 2, 3, 4])
    b = np.array([4, 2, 2, 4])
    c = np.array([1, 2, 3, 4])
    print(np.array_equal(a, b), np.array_equal(a, c))
    # False True

  def test_logic(self) -> None:
    a = np.array([1, 1, 0, 1], dtype=bool)
    b = np.array([1, 0, 1, 0], dtype=bool)
    print(np.logical_or(a, b), np.logical_and(a, b))
    # [ True  True  True  True] [ True False False False]

  # floating functions

  def test_floating(self) -> None:
    a = np.array([1, 3+4j])
    self.assertFalse(np.all(np.isreal(a)))

  # others
  def test_shape_not_match(self) -> None:
    a = np.arange(4)
    with self.assertRaises(ValueError) as cm:
      a + np.array([1, 2])
    self.assertEqual("operands could not be broadcast together with shapes (4,) (2,) ",
                     str(cm.exception))

  def test_transpose(self) -> None:
    a = np.triu(np.ones((3, 3)), 1)  # upper
    print(a)
    # [[0. 1. 1.]
    #  [0. 0. 1.]
    #  [0. 0. 0.]]
    print(a.T)
    # [[0. 0. 0.]
    #  [1. 0. 0.]
    #  [1. 1. 0.]]


class TestRedution(unittest.TestCase):
  def test_sum(self) -> None:
    x = np.array([1, 2, 3, 4])
    print(np.sum(x), x.sum())
    # 10 10

    x = np.array([[1, 1], [2, 2]])
    print(x, x.sum())
    # [[1 1]
    #  [2 2]] 6

    # axis=0: first dimension
    print(x.sum(axis=0))
    # [3 3]
    print(x[:, 0].sum(), x[:, 1].sum())
    # 3 3

    # axix=1: second dimension
    print(x.sum(axis=1))
    # [2 4]
    print(x[0, :].sum(), x[1, :].sum())
    # 2 4

  def test_min_max(self) -> None:
    x = np.array([1, 3, 2])
    print(x.min(), x.max(), x.argmin(), x.argmax())
    # 1 3 0 1

  def test_logic(self) -> None:
    print(np.all([True, True, False]), np.any([True, True, False]))
    # False True

  def test_statistic(self) -> None:
    x = np.array([1, 2, 3, 1])
    y = np.array([[1, 2, 3], [5, 6, 1]])

    print(x.mean(), np.median(x), np.median(y, axis=-1), x.std())
    # 1.75 1.5 [2. 5.] 0.82915619758885


class TestBroadcast(unittest.TestCase):
  def test_broadcast(self) -> None:
    # example: 9x9
    a = np.arange(1, 10, 1)
    print(a.shape, a[:, np.newaxis].shape)
    # (9,) (9, 1)

    # prepend axis to same dimension, copy-past to same size in dimension
    #    (9,) => (1,9) => (9,9)
    print(a * a[:, np.newaxis])
    # [[ 1  2  3  4  5  6  7  8  9]
    #  [ 2  4  6  8 10 12 14 16 18]
    #  [ 3  6  9 12 15 18 21 24 27]
    #  [ 4  8 12 16 20 24 28 32 36]
    #  [ 5 10 15 20 25 30 35 40 45]
    #  [ 6 12 18 24 30 36 42 48 54]
    #  [ 7 14 21 28 35 42 49 56 63]
    #  [ 8 16 24 32 40 48 56 64 72]
    #  [ 9 18 27 36 45 54 63 72 81]]

    # (9,) => (1,9)
    # print(a[np.newaxis, :]) # 1x9      <== prepend axis
    # print(a[:, np.newaxis]) # 9x1
    print(a[np.newaxis, :] * a[:, np.newaxis])
    # [[ 1  2  3  4  5  6  7  8  9]
    #  [ 2  4  6  8 10 12 14 16 18]
    #  [ 3  6  9 12 15 18 21 24 27]
    #  [ 4  8 12 16 20 24 28 32 36]
    #  [ 5 10 15 20 25 30 35 40 45]
    #  [ 6 12 18 24 30 36 42 48 54]
    #  [ 7 14 21 28 35 42 49 56 63]
    #  [ 8 16 24 32 40 48 56 64 72]
    #  [ 9 18 27 36 45 54 63 72 81]]

  def test_tile(self) -> None:
    a = np.arange(0, 40, 10)
    print(a)
    # [ 0 10 20 30]
    print(a.shape)
    # (4,)
    # (4,) =prepend 1 dimension=> (1,4) =same size in dimension=> (3, 4)
    print(np.tile(a, (3, 1)))
    # [[ 0 10 20 30]
    #  [ 0 10 20 30]
    #  [ 0 10 20 30]]

    b = np.array([[0], [1], [2]])
    print(b)
    # [[0]
    #  [1]
    #  [2]]
    print(b.shape)
    # (3, 1)
    # (4) =prepend 1 dimension=> (1, 4) =same size in dimension=> (3, 4)
    print(np.tile(b, (4)))
    # [[0 0 0 0]
    #  [1 1 1 1]
    #  [2 2 2 2]]


class TestShapeOp(unittest.TestCase):
  def test_ravel(self) -> None:
    # last dimension out first
    a = np.array([[1, 2, 3], [4, 5, 6]])
    print(a, a.ravel())
    # [[1 2 3]
    #  [4 5 6]] [1 2 3 4 5 6]
    print(a.T, a.T.ravel())
    # [[1 4]
    #  [2 5]
    #  [3 6]] [1 4 2 5 3 6]

  def test_reshape(self) -> None:
    a = np.array([[1, 2, 3], [4, 5, 6]])
    print(a)
    # [[1 2 3]
    #  [4 5 6]]
    print(a.reshape((3, -1)))  # -1: infer
    # [[1 2]
    #  [3 4]
    #  [5 6]]

  def test_newaix(self) -> None:
    z = np.array([1, 2, 3])
    print(z, z.shape)
    # [1 2 3] (3,)
    zz = z[:, np.newaxis]
    print(zz, zz.shape)
    # [[1]
    #  [2]
    #  [3]] (3, 1)
    zzz = z[np.newaxis, :]
    print(zzz, zzz.shape)
    # [[1 2 3]] (1, 3)

  def test_transpose(self) -> None:
    a = np.arange(4*3*2).reshape(4, 3, 2)
    print(a, a.shape)
    # [[[ 0  1]
    #   [ 2  3]
    #   [ 4  5]]

    #  [[ 6  7]
    #   [ 8  9]
    #   [10 11]]
    #
    #  [[12 13]
    #   [14 15]
    #   [16 17]]
    #
    #  [[18 19]
    #   [20 21]
    #   [22 23]]] (4, 3, 2)
    b = a.transpose(1, 2, 0)
    print(b, b.shape)
    # [[[ 0  6 12 18]
    #   [ 1  7 13 19]]
    #
    #  [[ 2  8 14 20]
    #   [ 3  9 15 21]]
    #
    #  [[ 4 10 16 22]
    #   [ 5 11 17 23]]] (3, 2, 4)

  def test_resize(self) -> None:
    a = np.arange(4)
    print(a)
    # [0 1 2 3]
    a.resize((8,))
    print(a)
    # [0 1 2 3 0 0 0 0]


class TestSort(unittest.TestCase):
  def test_sort(self) -> None:
    a = np.array([[4, 3, 5], [1, 2, 2]])
    b = np.sort(a, axis=1)
    print(a)
    # [[4 3 5]
    #  [1 2 2]]
    print(b)
    # [[3 4 5]
    #  [1 2 2]]

  def test_sort_inplace(self) -> None:
    a = np.array([[4, 3, 5], [1, 2, 2]])
    a.sort(axis=1)
    print(a)
    # [[3 4 5]
    #  [1 2 2]]

  def test_sort_with_index(self) -> None:
    a = np.array([4, 3, 1, 2])
    j = np.argsort(a)
    print(j)
    # [2 3 1 0]
    print(a[j])
    # [1 2 3 4]

    # max, min
    a = np.array([4, 3, 1, 2])
    j_max = np.argmax(a)
    j_min = np.argmin(a)
    print(j_max, j_min)
    # 0 2
    print(a[j_max], a[j_min])
    # 4 1
