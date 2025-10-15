"""
Tensor operations
"""

import numpy as np


def navie_relu(x: np.ndarray):
  """relu"""
  assert len(x.shape) == 2
  x = x.copy()  # avoid overwrite x
  for i in range(x.shape[0]):
    for j in range(x.shape[1]):
      x[i, j] = max(x[i, j], 0)
  return x


def navie_add(x: np.ndarray, y: np.ndarray):
  """add"""
  assert len(x.shape) == 2
  assert x.shape == y.shape
  x = x.copy()
  for i in range(x.shape[0]):
    for j in range(x.shape[1]):
      x[i, j] += y[i, j]
  return x


def navie_add_matrix_and_vector(x: np.ndarray, y: np.ndarray):
  """broadcasting: add matrix and vector"""
  assert len(x.shape) == 2
  assert len(y.shape) == 1
  assert x.shape[1] == y.shape[0]

  x = x.copy()
  for i in range(x.shape[0]):
    for j in range(x.shape[1]):
      x[i, j] += y[j]
  return x


def navie_vector_dot(x: np.ndarray, y: np.ndarray):
  """vector product"""
  # x, y are Numpy vectors
  assert len(x.shape) == 1
  assert len(y.shape) == 1
  assert x.shape[0] == y.shape[0]
  z = 0.
  for i in range(x.shape[0]):
    z += x[i] * y[i]
  return z


def navie_matrix_vector_dot(x: np.ndarray, y: np.ndarray):
  """matrix-vector product"""
  assert len(x.shape) == 2
  assert len(y.shape) == 1
  assert x.shape[1] == y.shape[0]

  z = np.zeros(x.shape[0])
  for i in range(x.shape[0]):
    for j in range(x.shape[1]):
      z[i] += x[i, j] * y[j]
  return z


def navie_matrix_dot(x: np.ndarray, y: np.ndarray):
  """matrix-vector product"""
  assert len(x.shape) == 2  # (a,b)
  assert len(y.shape) == 2  # (b,c)
  assert x.shape[1] == y.shape[0]

  z = np.zeros((x.shape[0], y.shape[1]))
  for i in range(x.shape[0]):
    for j in range(y.shape[1]):
      row_x = x[i, :]
      column_y = y[:, j]
      z[i, j] = navie_vector_dot(row_x, column_y)
  return z
