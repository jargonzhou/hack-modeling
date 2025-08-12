# NumPy
* http://numpy.org/
* citing: https://numpy.org/citing-numpy
* [API reference](https://numpy.org/doc/stable/reference/index.html)
** [Array objects](https://numpy.org/doc/stable/reference/arrays.html)
** [Universal functions](https://numpy.org/doc/stable/reference/ufuncs.html)
** [Explanations - Broadcasting](https://numpy.org/doc/stable/user/basics.broadcasting.html)

NumPy: Numerical Python

NumPy is the fundamental package for scientific computing with Python.

It provides:

* a powerful N-dimensional array object
* sophisticated (broadcasting) functions
* tools for integrating C/C++ and Fortran code
* useful linear algebra, Fourier transform, and random number capabilities


<<<.tc-big-quote

<<<


# Data Type

* `int8`, `uint8`: `i1`, `u1`
* `int16`, `uint16`: `i2`, `u2`
* `int32`, `uint32`: `i4`, `u4`
* `int64`, `uint64`: `i8`, `u8`
* `float16`: `f2`
* `float32`: `f4`, `f`
* `float64`: `f8`, `d`
* `float128`: `f16`, `g`
* `complex64`, `complex128`, `complex256`: `c8`, `c16` `c32`
* `bool`
* `object`
* ~~`string_`: `S`~~ `np.string_` was removed in the NumPy 2.0 release. Use `np.bytes_` instead.
* `unicode_`: `U`

# Usage

Action: `jupyter-notebooks/DataEngineering/_DataScience/tools/numpy/_numpy.ipynb`

```python
import numpy as np
```

## Array objects
### `ndarray`

* Attributes
* Methods
** array creation
** shape manipulation
** item selection and manipulation
** calculation
* Arithmetic, matrix multiplication, and comparison operations
** comparison operator
** truth value of array
** unary operator
** arithmetic (in-place)
** matrix multiplication
* Special methods

## ufunc

* math operations
* trigonometric functions
* bit-twiddling functions
* comparison functions
* floating functions

## Output

```python
np.get_printoptions()

np.save()
np.savez()
np.savez_compressed()
```

## `numpy.random`

* `permutation`: Return a random permutation of a sequence, or return a permuted range
* `shuffle`: Randomly permute a sequence in place
* `uniform`: Draw samples from a uniform distribution
* `integers`: Draw random integers from a given low-to-high range
* `standard_normal`: Draw samples from a normal distribution with mean 0 and standard deviation 1
* `binomial`: Draw samples from a binomial distribution
* `normal`: Draw samples from a normal (Gaussian) distribution
* `beta`: Draw samples from a beta distribution
* `chisquare`: Draw samples from a chi-square distribution
* `gamma`: Draw samples from a gamma distribution
* `uniform`: Draw samples from a uniform [0, 1) distribution

## `numpy.linalg`

* `@` operator
* matrix and vector product
* decompositions
* matrix eigenvalues
* norms
* inverting matrix

## `numpy.fft`

> TODO

# See Also

* [Numba](./Numba.md)


