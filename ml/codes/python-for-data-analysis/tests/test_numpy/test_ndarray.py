"""
Unit test of Numpy ndarray.
"""

import unittest
import numpy as np

# pylint: skip-file


class TestModule(unittest.TestCase):
  def test_version(self) -> None:
    print(np.__version__)
    # 2.3.2

  def test_submodule(self) -> None:
    print(np.__numpy_submodules__)
    # {'exceptions', 'rec', 'core', 'linalg', 'f2py', 'fft', 'ma', 'strings', 'ctypeslib', 'random', 'typing', 'polynomial', 'char', 'lib', 'testing', 'dtypes', 'test'}


class TestNDArray(unittest.TestCase):
  def test_create(self) -> None:
    # array()
    # arange()
    # linspace()
    # ones()
    # zeros()
    # eye()
    # diag()
    # random
    pass

  def test_dtype(self) -> None:
    self.assertEqual(np.dtype('int64'), np.array([1, 2, 3]).dtype)
    self.assertEqual(np.dtype('float64'), np.array([1., 2., 3.]).dtype)
    self.assertEqual(np.dtype('float64'),
                     np.array([1, 2, 3], dtype=float).dtype)
    self.assertEqual(np.dtype('complex128'),
                     np.array([1+2j, 3+4j, 5+6j]).dtype)
    self.assertEqual(np.dtype('bool'),
                     np.array([True, False, False, True]).dtype)
    self.assertEqual(np.dtype('<U7'),
                     np.array(['Bonjour', 'Hello', '你好']).dtype)

    # cast
    self.assertEqual(np.dtype('float64'),
                     (np.array([1, 2, 3]) + 1.5).dtype)
    self.assertEqual(np.dtype('int64'),
                     np.array([1.7, 1.2, 1.6]).astype(int).dtype)

    # info
    print(np.iinfo(np.int32).max, np.iinfo(np.uint32).max)
    # 2147483647 4294967295
    print(np.finfo(np.float32).eps, np.finfo(np.float64).eps)
    # 1.1920929e-07 2.220446049250313e-16

  def test_str_representation(self) -> None:
    A = np.matrix(np.array([[2, 2], [2, 2]]))
    B = np.matrix(np.array([[1, 1], [1, 1]]))
    C = np.bmat('A B; B A')
    # can we just use??? see test_str_representation
    # [[2 2 1 1]
    #  [2 2 1 1]
    #  [1 1 2 2]
    #  [1 1 2 2]]
    raw_data: str = """
    [[2 2 1 1]
     [2 2 1 1]
     [1 1 2 2]
     [1 1 2 2]]"""
    from src.python_for_data_analysis.util.parse import from_string
    np.testing.assert_array_equal(C,
                                  from_string(raw_data, np.int32, 4*4, (4, 4)))

  def test_indexing(self) -> None:
    # 1-d
    a = np.arange(10)
    print(a)
    # [0 1 2 3 4 5 6 7 8 9]
    print(a[0], a[2], a[-1])
    # 0 2 9
    print(a[::2], a[::-1])
    # [0 2 4 6 8] [9 8 7 6 5 4 3 2 1 0]
    print(a[2:9:3])
    # [2 5 8]
    print(a[1:3], a[::2], a[3:])
    # [1 2] [0 2 4 6 8] [3 4 5 6 7 8 9]

    # 2-d
    a = np.diag(np.arange(3))
    print(a)
    # [[0 0 0]
    #  [0 1 0]
    #  [0 0 2]]
    print(a[1, 1])
    # 1
    print(a[1])
    # [0 1 0]

    aa = np.arange(56).reshape(7, 8)
    print(aa)
    # [[ 0  1  2  3  4  5  6  7]
    #  [ 8  9 10 11 12 13 14 15]
    #  [16 17 18 19 20 21 22 23]
    #  [24 25 26 27 28 29 30 31]
    #  [32 33 34 35 36 37 38 39]
    #  [40 41 42 43 44 45 46 47]
    #  [48 49 50 51 52 53 54 55]]
    print(aa[0, 3:5])
    # [3 4]
    print(aa[4:, 4:])
    # [[36 37 38 39]
    #  [44 45 46 47]
    #  [52 53 54 55]]
    print(aa[:, 2])
    # [ 2 10 18 26 34 42 50]

  def test_bool_mask(self) -> None:
    np.random.seed(3)
    a = np.random.randint(0, 21, 15)
    print(a)
    # [10  3  8  0 19 10 11  9 10  6  0 20 12  7 14]

    mask = a % 3 == 0
    print(a[mask])
    # [ 3  0  9  6  0 12]

    a[a % 3 == 0] = -1  # assignment
    print(a)
    # [10 -1  8 -1 19 10 11 -1 10 -1 -1 20 -1  7 14]

  def test_indexing_wit_int_array(self) -> None:
    a = np.arange(0, 100, 10)
    print(a)
    # [ 0 10 20 30 40 50 60 70 80 90]
    # Python list
    print(a[[2, 3, 2, 4, 2]])
    # [20 30 20 40 20]
    # assignment
    a[[9, 7]] = -100
    print(a)
    # [   0   10   20   30   40   50   60 -100   80 -100]

    # ndarray: with index shape
    a = np.arange(10)
    idx = np.array([[3, 4], [9, 2]])
    print(a, idx)
    # [0 1 2 3 4 5 6 7 8 9] [[3 4]
    #  [9 2]]
    print(a[idx])
    # [[3 4]
    #  [9 2]]

  def test_copy_view(self) -> None:
    a = np.arange(10)
    # view: slicing
    b = a[::2]
    self.assertTrue(np.may_share_memory(a, b))
    b[0] = 12
    self.assertTrue(np.may_share_memory(a, b))
    self.assertEqual(a[0], b[0])

    # copy
    c = a[::2].copy()
    self.assertFalse(np.may_share_memory(a, c))
    c[0] = 13
    self.assertEqual(13, c[0])
    self.assertNotEqual(c[0], a[0])


class TestMatrixObject(unittest.TestCase):
  def test_create(self) -> None:
    a = np.matrix([[1, 5, 10], [1.0, 3, 4j]])  # type: ignore[arg-type]
    print(a)
    a = np.matrix(np.array([[1, 5, 10], [1.0, 3, 4j]]))
    print(a)
    a = np.matrix('1 5 10; 1.0 3 4j')
    print(a)
    np.testing.assert_array_almost_equal(np.array([[1, 5, 10], [1.0, 3, 4j]]),
                                         np.matrix('1 5 10; 1.0 3 4j'))

    a = np.matrix(np.random.rand(3, 3)).T
    print(a)

    A = np.matrix(np.array([[2, 2], [2, 2]]))
    B = np.matrix(np.array([[1, 1], [1, 1]]))
    C = np.bmat('A B; B A')
    # can we just use str representation
    # [[2 2 1 1]
    #  [2 2 1 1]
    #  [1 1 2 2]
    #  [1 1 2 2]]
    np.testing.assert_array_equal([[2, 2, 1, 1],
                                   [2, 2, 1, 1],
                                   [1, 1, 2, 2],
                                   [1, 1, 2, 2]],
                                  C)


class TestMemoryMappedFileArray(unittest.TestCase):
  # memmap
  def test_memmap(self) -> None:
    file_name = 'newfile.dat'
    # a = np.arange(1000, dtype=np.float64)
    # np.save(file_name, a)

    a = np.memmap(file_name, dtype=np.float64, mode='w+', shape=100)

    a[10] = 10.0
    a[30] = 30.0
    del a

    b = np.fromfile(file_name, dtype=np.float64)
    self.assertAlmostEqual(10.0, b[10])
    self.assertAlmostEqual(30.0, b[30])

    a = np.memmap(file_name, dtype=np.float64)
    self.assertAlmostEqual(10.0, a[10])
    self.assertAlmostEqual(30.0, a[30])

    # clean up
    del b
    del a
    import os
    os.remove(file_name)


class TestCharacterArray(unittest.TestCase):
  # numpy.char
  def test_char_array(self) -> None:
    ca = np.char.array("hello numpy".split())
    print(ca)


class TestRecordArray(unittest.TestCase):
  # numpy.rec
  def test_record_array(self) -> None:
    desc = np.dtype({'names': ['name', 'age', 'weight'],
                     'formats': ['S30', 'int8', 'float64']})
    ra = np.array([('Bill', 31, 26.0),
                   ('Fred', 15, 145.0)], dtype=desc)
    print(ra, '\n',
          ra[0], '\n',
          ra['name'], '\n',
          ra['age'], '\n',
          ra['weight'], '\n',
          ra[0]['name'])
    # [(b'Bill', 31,  26.) (b'Fred', 15, 145.)]
    #  (b'Bill', 31, 26.0)
    #  [b'Bill' b'Fred']
    #  [31 15]
    #  [ 26. 145.]
    #  b'Bill'
    self.assertEqual(b'Bill', ra[0]['name'])
    self.assertEqual(3, len(ra[0]))

    # get record array
    print(type(ra), type(ra.view(np.recarray)), ra.view(np.recarray))
    # <class 'numpy.ndarray'> <class 'numpy.rec.recarray'> [(b'Bill', 31,  26.) (b'Fred', 15, 145.)]


class TestMaskedArray(unittest.TestCase):
  # numpy.ma
  def test_create(self) -> None:
    x = np.ma.array([1, 2, 3, 4], mask=[0, 1, 0, 1])
    print(x, x + 1, x[0])
    # [1 -- 3 --] [2 -- 4 --] 1
    print(np.ma.sqrt([1, -1, 2, -2]))
    # [1.0 -- 1.4142135623730951 --]


class TestUserArray(unittest.TestCase):
  # numpy.lib.user_array.container
  def test_create(self) -> None:
    from numpy.lib.user_array import container
    x = container(np.array([[1, 2], [3, 4]]))
    print(x)
    # container([[1, 2],
    #    [3, 4]])
    self.assertIsInstance(x.array, np.ndarray)


class TestArrayIterator(unittest.TestCase):
  def test_deault_iteration(self) -> None:
    a = np.arange(24).reshape(3, 2, 4) + 10
    for val in a:
      print(val)
    # [[10 11 12 13]
    #  [14 15 16 17]]
    # [[18 19 20 21]
    #  [22 23 24 25]]
    # [[26 27 28 29]
    #  [30 31 32 33]]

  def test_flat_iteration(self) -> None:
    a = np.arange(24).reshape(3, 2, 4) + 10
    for i, val in enumerate(a.flat):
      if i % 5 == 0:
        print(i, val)
    # 0 10
    # 5 15
    # 10 20
    # 15 25
    # 20 30

  def test_ndimensional_enumeration(self) -> None:
    a = np.arange(24).reshape(3, 2, 4) + 10
    for i, val in np.ndenumerate(a):
      if sum(i) % 5 == 0:
        print(i, val)
    # (0, 0, 0) 10
    # (1, 1, 3) 25
    # (2, 0, 3) 29
    # (2, 1, 2) 32

  def test_broadcast_iterator(self) -> None:
    a = np.broadcast([[1, 0], [2, 3]],
                     [0, 1])
    print(a)
    # <numpy.broadcast object at 0x0000012FCF727490>
    for val in a:
      print(val)
    # (np.int64(1), np.int64(0))
    # (np.int64(0), np.int64(1))
    # (np.int64(2), np.int64(0)) <- 2 0
    # (np.int64(3), np.int64(1)) <- 3 1
    print()
    for val in np.broadcast([[1, 0], [2, 3]],
                            [[0, 1], [0, 1]]):
      print(val)
    # (np.int64(1), np.int64(0))
    # (np.int64(0), np.int64(1))
    # (np.int64(2), np.int64(0))
    # (np.int64(3), np.int64(1))


class TestStorage(unittest.TestCase):
  def test_txt(self) -> None:
    data = np.array([[1900, 30000, 4000, 48300],
                     [1901, 47200, 6100, 48200],
                     [1902, 70200, 9800, 41500]])
    file_path = 'data/population.txt'
    np.savetxt(file_path, data)
    data2 = np.loadtxt(file_path)
    np.testing.assert_array_equal(data, data2)

    # cleanup
    import os
    os.remove(file_path)

  def test_npy(self) -> None:
    data = np.ones((3, 3))
    data_path = 'data/population.npy'
    np.save(data_path, data)
    data2 = np.load(data_path)
    np.testing.assert_array_equal(data2, data)

    # cleanup
    import os
    os.remove(data_path)

  def test_image(self) -> None:
    import matplotlib.pyplot as plt
    img = plt.imread('data/elephant.jpg')
    print(img.shape, img.dtype)
    # (240, 160, 3) uint8

    plt.imshow(img)
    img_path1 = 'data/plot.png'
    plt.savefig(img_path1)
    img_path2 = 'data/plot2.png'
    plt.imsave(img_path2, img[:, :, 0], cmap=plt.cm.get_cmap('gray'))

    # cleanup
    import os
    os.remove(img_path1)
    os.remove(img_path2)


class TestPlot(unittest.TestCase):
  def test_matplotlib(self) -> None:
    import matplotlib.pyplot as plt
    x = np.linspace(0, 3, 20)
    y = np.linspace(0, 9, 20)
    plt.plot(x, y)
    plt.plot(x, y, 'o')
    plt.show()

    image = np.random.rand(30, 30)
    plt.imshow(image, cmap=plt.cm.get_cmap('hot'))
    plt.colorbar()
    plt.show()


class TestPolynomial(unittest.TestCase):
  # numpy.polynomial
  def test_poly1d(self) -> None:
    p = np.poly1d([3, 2, -1])  # 3 x^2 + 2 x - 1
    print(p)
    print(p(0), p.roots, p.order)
    # 3 x + 2 x - 1
    # -1 [-1.          0.33333333] 2

  def test_polyfit(self) -> None:
    x = np.linspace(0, 1, 20)
    y = np.cos(x) + 0.3*np.random.rand(20)

    p = np.poly1d(np.polyfit(x, y, 3))  # 多项式拟合
    t = np.linspace(0, 1, 200)
    import matplotlib.pyplot as plt
    plt.plot(x, y, 'o', t, p(t), '-')
    plt.show()

  def test_polynomial(self) -> None:
    p = np.polynomial.Polynomial([-1, 2, 3])
    print(p(0), p.roots(), p.degree())
    # -1.0 [-1.          0.33333333] 2

  def test_Chebyshev(self) -> None:
    x = np.linspace(-1, 1, 2000)
    y = np.cos(x) + 0.3*np.random.rand(2000)
    p = np.polynomial.Chebyshev.fit(x, y, 90)  # 拟合

    t = np.linspace(-1, 1, 2000)
    import matplotlib.pyplot as plt
    plt.plot(x, y, 'r.', t, p(t), 'k-')
    plt.show()
