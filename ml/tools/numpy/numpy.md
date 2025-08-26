# NumPy
* http://numpy.org/
* https://github.com/numpy/numpy
* citing: https://numpy.org/citing-numpy

> NumPy: Numerical Python
>
> NumPy is the fundamental package for scientific computing with Python.
>
> It provides:
>
> * a powerful N-dimensional array object
> * sophisticated (broadcasting) functions
> * tools for integrating C/C++ and Fortran code
> * useful linear algebra, Fourier transform, and random number capabilities

```python
import numpy as np
```

books/articles:
- Guide to NumPy, 2006
- Array programming with NumPy, 2020
- Python for Data Analysis: Data Wrangling with pandas, NumPy & Jupyter, 2022

# Library Organization
* core: `ndarray` data structure, universal functions.
* computing libraries: functions for array manipulation and scientific computation.
* infrastructure libraries: unit tests, Python package building.
* F2PY: wrap Fortran code in Python.

# NEP(NumPy Enhancement Proposal)
* https://numpy.org/neps/
* https://numpy.org/neps/nep-0000.html

# Array Concepts

[](./image/numpy.fundamental%20array%20concepts.png)

fundamental array concepts:
- data structure: data, data type, shape, strides
- indexing
  - view: slice `start:end:step`
  - copy: scalar, mask, array, broadcasting
- vectorization
- broadcasting
- reduction

array proliferation
- GPU arrays: PyTorch, Tensoflow, Apache MXNet, JAX
- spare arrays: Scipy, PyData [sparse](https://github.com/pydata/sparse)
- distributed arrays: Dask
- labeled arrays: PyData [xarray](https://github.com/pydata/xarray)

array function protocol: Numpy-like API interoperability
- `__array_ufunc__` protocol: 1.13
- `__array_function__` protocol: 1.17
- projects
  - [Cupy](https://cupy.chainer.org/): NumPy/SciPy-compatible Array Library for GPU-accelerated Computing with Python
  - [JAX](https://jax.readthedocs.io/en/latest/jax.numpy.html): JAX is a Python library for accelerator-oriented array computation and program transformation, designed for high-performance numerical computing and large-scale machine learning.
  - [Apache MXNet](https://numpy.mxnet.io/): Lightweight, Portable, Flexible Distributed/Mobile Deep Learning with Dynamic, Mutation-aware Dataflow Dep Scheduler; for Python, R, Julia, Scala, Go, Javascript and more. MXNet retired in September 2023 and the move to [the Attic](https://attic.apache.org/projects/mxnet.html) was completed in February 2024.
  - [PyTorch](https://pytorch.org/tutorials/beginner/blitz/tensor_tutorial.html)
  - [Tensorflow](https://www.tensorflow.org/tutorials/customization/basics)
  - [Dask](https://github.com/dask/dask): Dask is a flexible parallel computing library for analytics.


# `numpy`
* https://numpy.org/doc/stable/reference/index.html

topics on routines and objects
- Constants
- Array creation routines
- Array manipulation routines
- Bit-wise operations
- String functionality
- Datetime support functions
- Data type routines
- Mathematical functions with automatic domain
- Floating point error handling
- Exceptions and Warnings
- Discrete Fourier Transform
- Functional programming
- Input and output
- Indexing routines
- Linear algebra
- Logic functions
- Masked array operations
- Mathematical functions
- Miscellaneous routines
- Polynomials
- Random sampling
- Set routines
- Sorting, searching, and counting
- Statistics
- Test support
- Window functions

## `dir(numpy)`

catrogory notation
* create: creating arrays
* op 2 arrays: operations on two or more arrays
* print: printing arrays
* data type: dealing with data types
* shape: shape functions
* basic: basic functions
* polynomial: polynomial functions
* set: set operation
* indexing: array construction using index trick
* 2d: two-dimensional
* like ufunc: functions behave like ufuncs
* misc: miscellaneous functions
* utility: utility functions
* matrix: matrix object


| Category    | Method                  | Description |
| :---------- | :---------------------- | :---------- |
|             | False_                  |             |
|             | ScalarType              |             |
|             | True_                   |             |
|             | _CopyMode               |             |
|             | _NoValue                |             |
|             | _array_api_info         |             |
|             | _core                   |             |
|             | _distributor_init       |             |
|             | _expired_attrs_2_0      |             |
|             | _globals                |             |
|             | _int_extended_msg       |             |
|             | _mat                    |             |
|             | _msg                    |             |
|             | _pyinstaller_hooks_dir  |             |
|             | _pytesttester           |             |
|             | _specific_msg           |             |
|             | _type_info              |             |
|             | _typing                 |             |
|             | _utils                  |             |
|             | abs                     |             |
|             | absolute                |             |
|             | acos                    |             |
|             | acosh                   |             |
|             | add                     |             |
|             | all                     |             |
| op 2 arrays | allclose                |             |
|             | amax                    |             |
|             | amin                    |             |
| basic       | angle                   |             |
|             | any                     |             |
| basic       | append                  |             |
| shape       | apply_along_axis        |             |
| shape       | apply_over_axes         |             |
| create      | arange                  |             |
|             | arccos                  |             |
|             | arccosh                 |             |
|             | arcsin                  |             |
|             | arcsinh                 |             |
|             | arctan                  |             |
|             | arctan2                 |             |
|             | arctanh                 |             |
|             | argmax                  |             |
|             | argmin                  |             |
|             | argpartition            |             |
|             | argsort                 |             |
|             | argwhere                |             |
|             | around                  |             |
| create      | array                   |             |
| print       | array2string            |             |
|             | array_equal             |             |
|             | array_equiv             |             |
|             | array_repr              |             |
| shape       | array_split             |             |
|             | array_str               |             |
| create      | asanyarray              |             |
|             | asarray                 |             |
| basic       | asarray_chkfinite       |             |
|             | ascontiguousarray       |             |
|             | asfortranarray          |             |
|             | asin                    |             |
|             | asinh                   |             |
| matrix      | asmatrix                |             |
|             | astype                  |             |
|             | atan                    |             |
|             | atan2                   |             |
|             | atanh                   |             |
| shape       | atleast_1d              |             |
| shape       | atleast_2d              |             |
| shape       | atleast_3d              |             |
| basic       | average                 |             |
| misc        | bartlett                |             |
|             | base_repr               |             |
|             | binary_repr             |             |
| basic       | bincount                |             |
|             | bitwise_and             |             |
|             | bitwise_count           |             |
|             | bitwise_invert          |             |
|             | bitwise_left_shift      |             |
|             | bitwise_not             |             |
|             | bitwise_or              |             |
|             | bitwise_right_shift     |             |
|             | bitwise_xor             |             |
| misc        | blackman                |             |
|             | block                   |             |
| 2d,matrix   | bmat                    |             |
|             | bool                    |             |
|             | bool_                   |             |
|             | broadcast               |             |
|             | broadcast_arrays        |             |
|             | broadcast_shapes        |             |
|             | broadcast_to            |             |
|             | busday_count            |             |
|             | busday_offset           |             |
|             | busdaycalendar          |             |
|             | byte                    |             |
|             | bytes_                  |             |
| index trick | c_                      |             |
| data type   | can_cast                |             |
|             | cbrt                    |             |
|             | cdouble                 |             |
|             | ceil                    |             |
|             | char                    |             |
|             | character               |             |
|             | choose                  |             |
|             | clip                    |             |
|             | clongdouble             |             |
| shape       | column_stack            |             |
|             | common_type             |             |
|             | complex128              |             |
|             | complex64               |             |
|             | complexfloating         |             |
|             | compress                |             |
|             | concat                  |             |
| op 2 arrays | concatenate             |             |
|             | conj                    |             |
|             | conjugate               |             |
| op 2 arrays | convolve                |             |
|             | copy                    |             |
|             | copysign                |             |
|             | copyto                  |             |
|             | core                    |             |
| basic       | corrcoef                |             |
| op 2 arrays | correlate               |             |
|             | cos                     |             |
|             | cosh                    |             |
|             | count_nonzero           |             |
| basic       | cov                     |             |
| op 2 arrays | cross                   |             |
|             | csingle                 |             |
|             | ctypeslib               |             |
|             | cumprod                 |             |
|             | cumsum                  |             |
|             | cumulative_prod         |             |
|             | cumulative_sum          |             |
|             | datetime64              |             |
|             | datetime_as_string      |             |
|             | datetime_data           |             |
|             | deg2rad                 |             |
|             | degrees                 |             |
| basic       | delete                  |             |
| 2d          | diag                    |             |
|             | diag_indices            |             |
|             | diag_indices_from       |             |
| 2d          | diagflat                |             |
|             | diagonal                |             |
| basic       | diff                    |             |
| basic       | digitize                |             |
|             | divide                  |             |
|             | divmod                  |             |
| op 2 arrays | dot                     |             |
|             | double                  |             |
| shape       | dsplit                  |             |
| shape       | dstack                  |             |
| data type   | dtype                   |             |
|             | dtypes                  |             |
|             | e                       |             |
|             | ediff1d                 |             |
|             | einsum                  |             |
|             | einsum_path             |             |
|             | emath                   |             |
| create      | empty                   |             |
| create      | empty_like              |             |
|             | equal                   |             |
|             | errstate                |             |
|             | euler_gamma             |             |
|             | exceptions              |             |
|             | exp                     |             |
|             | exp2                    |             |
| shape       | expand_dims             |             |
|             | expm1                   |             |
| basic       | extract                 |             |
| 2d          | eye                     |             |
|             | f2py                    |             |
|             | fabs                    |             |
|             | fft                     |             |
|             | fill_diagonal           |             |
| data type   | finfo                   |             |
| like ufunc  | fix                     |             |
|             | flatiter                |             |
| create      | flatnonzero             |             |
|             | flexible                |             |
|             | flip                    |             |
| 2d          | fliplr                  |             |
| 2d          | flipud                  |             |
|             | float16                 |             |
|             | float32                 |             |
|             | float64                 |             |
|             | float_power             |             |
|             | floating                |             |
|             | floor                   |             |
|             | floor_divide            |             |
|             | fmax                    |             |
|             | fmin                    |             |
|             | fmod                    |             |
|             | format_float_positional |             |
|             | format_float_scientific |             |
|             | frexp                   |             |
|             | from_dlpack             |             |
| create      | frombuffer              |             |
| create      | fromfile                |             |
| create      | fromfunction            |             |
| create      | fromiter                |             |
|             | frompyfunc              |             |
|             | fromregex               |             |
| create      | fromstring              |             |
|             | full                    |             |
|             | full_like               |             |
|             | gcd                     |             |
|             | generic                 |             |
|             | genfromtxt              |             |
|             | geomspace               |             |
| utility     | get_include             |             |
| print       | get_printoptions        |             |
|             | getbufsize              |             |
|             | geterr                  |             |
|             | geterrcall              |             |
| basic       | gradient                |             |
|             | greater                 |             |
|             | greater_equal           |             |
|             | half                    |             |
| misc        | hamming                 |             |
| misc        | hanning                 |             |
|             | heaviside               |             |
| basic       | histogram               |             |
| basic       | histogram2d             |             |
|             | histogram_bin_edges     |             |
| basic       | histogramdd             |             |
| shape       | hsplit                  |             |
| shape       | hstack                  |             |
|             | hypot                   |             |
| misc        | i0                      |             |
| create      | identity                |             |
|             | iinfo                   |             |
|             | imag                    |             |
|             | in1d                    |             |
| indexing    | index_exp               |             |
| create      | indices                 |             |
|             | inexact                 |             |
|             | inf                     |             |
|             | info                    |             |
| op 2 arrays | inner                   |             |
| basic       | insert                  |             |
|             | int16                   |             |
|             | int32                   |             |
|             | int64                   |             |
|             | int8                    |             |
|             | int_                    |             |
|             | intc                    |             |
|             | integer                 |             |
|             | interp                  |             |
| set         | intersect1d             |             |
|             | intp                    |             |
|             | invert                  |             |
|             | is_busday               |             |
|             | isclose                 |             |
|             | iscomplex               |             |
| data type   | iscomplexobj            |             |
| data type   | isdtype                 |             |
|             | isfinite                |             |
| create      | isfortran               |             |
|             | isin                    |             |
|             | isinf                   |             |
|             | isnan                   |             |
|             | isnat                   |             |
| like ufunc  | isneginf                |             |
| like ufunc  | isposinf                |             |
|             | isreal                  |             |
| data type   | isrealobj               |             |
| data type   | isscalar                |             |
| data type   | issubdtype              |             |
|             | iterable                |             |
| index trick | ix_                     |             |
| misc        | kaiser                  |             |
| shape       | kron                    |             |
|             | lcm                     |             |
|             | ldexp                   |             |
|             | left_shift              |             |
|             | less                    |             |
|             | less_equal              |             |
| create      | lexsort                 |             |
|             | lib                     |             |
|             | linalg                  |             |
| basic       | linspace                |             |
|             | little_endian           |             |
| create      | load                    |             |
|             | loadtxt                 |             |
|             | log                     |             |
|             | log10                   |             |
|             | log1p                   |             |
| like ufunc  | log2                    |             |
|             | logaddexp               |             |
|             | logaddexp2              |             |
|             | logical_and             |             |
|             | logical_not             |             |
|             | logical_or              |             |
|             | logical_xor             |             |
| basic       | logspace                |             |
|             | long                    |             |
|             | longdouble              |             |
|             | longlong                |             |
|             | ma                      |             |
|             | mask_indices            |             |
|             | matmul                  |             |
| matrix      | matrix                  |             |
|             | matrix_transpose        |             |
|             | matvec                  |             |
|             | max                     |             |
|             | maximum                 |             |
|             | may_share_memory        |             |
|             | mean                    |             |
| basic       | median                  |             |
|             | memmap                  |             |
| basic       | meshgrid                |             |
| index trick | mgrid                   |             |
|             | min                     |             |
|             | min_scalar_type         |             |
|             | minimum                 |             |
| data type   | mintypecode             |             |
|             | mod                     |             |
|             | modf                    |             |
|             | moveaxis                |             |
|             | multiply                |             |
|             | nan                     |             |
| data type   | nan_to_num              |             |
| basic       | nanargmax               |             |
| basic       | nanargmin               |             |
|             | nancumprod              |             |
|             | nancumsum               |             |
| basic       | nanmax                  |             |
|             | nanmean                 |             |
|             | nanmedian               |             |
| basic       | nanmin                  |             |
|             | nanpercentile           |             |
|             | nanprod                 |             |
|             | nanquantile             |             |
|             | nanstd                  |             |
| basic       | nansum                  |             |
|             | nanvar                  |             |
|             | ndarray                 |             |
|             | ndenumerate             |             |
|             | ndim                    |             |
| indexing    | ndindex                 |             |
|             | nditer                  |             |
|             | negative                |             |
|             | nested_iters            |             |
|             | newaxis                 |             |
|             | nextafter               |             |
|             | nonzero                 |             |
|             | not_equal               |             |
|             | number                  |             |
|             | object_                 |             |
| index trick | ogrid                   |             |
| create      | ones                    |             |
| create      | ones_like               |             |
| op 2 arrays | outer                   |             |
|             | packbits                |             |
|             | pad                     |             |
|             | partition               |             |
|             | percentile              |             |
|             | permute_dims            |             |
|             | pi                      |             |
| basic       | piecewise               |             |
| basic       | place                   |             |
| polynomial  | poly                    |             |
| polynomial  | poly1d                  |             |
| polynomial  | polyadd                 |             |
| polynomial  | polyder                 |             |
| polynomial  | polydiv                 |             |
| polynomial  | polyfit                 |             |
| polynomial  | polyint                 |             |
| polynomial  | polymul                 |             |
|             | polynomial              |             |
| polynomial  | polysub                 |             |
| polynomial  | polyval                 |             |
|             | positive                |             |
|             | pow                     |             |
|             | power                   |             |
|             | printoptions            |             |
|             | prod                    |             |
|             | promote_types           |             |
|             | ptp                     |             |
|             | put                     |             |
|             | put_along_axis          |             |
| create      | putmask                 |             |
|             | quantile                |             |
| index trick | r_                      |             |
|             | rad2deg                 |             |
|             | radians                 |             |
|             | random                  |             |
|             | ravel                   |             |
|             | ravel_multi_index       |             |
|             | real                    |             |
| data type   | real_if_close           |             |
|             | rec                     |             |
|             | recarray                |             |
|             | reciprocal              |             |
|             | record                  |             |
|             | remainder               |             |
|             | repeat                  |             |
| create      | require                 |             |
|             | reshape                 |             |
| shape       | resize                  |             |
|             | result_type             |             |
|             | right_shift             |             |
|             | rint                    |             |
| shape       | roll                    |             |
| shape       | rollaxis                |             |
| polynomial  | roots                   |             |
| 2d          | rot90                   |             |
| basic       | round                   |             |
| shape       | row_stack               |             |
| indexing    | s_                      |             |
|             | save                    |             |
|             | savetxt                 |             |
|             | savez                   |             |
|             | savez_compressed        |             |
|             | sctypeDict              |             |
|             | searchsorted            |             |
| basic       | select                  |             |
| print       | set_printoptions        |             |
|             | setbufsize              |             |
| set         | setdiff1d               |             |
|             | seterr                  |             |
|             | seterrcall              |             |
| set         | setxor1d                |             |
|             | shape                   |             |
|             | shares_memory           |             |
|             | short                   |             |
|             | show_config             |             |
|             | show_runtime            |             |
|             | sign                    |             |
|             | signbit                 |             |
|             | signedinteger           |             |
|             | sin                     |             |
| misc        | sinc                    |             |
|             | single                  |             |
|             | sinh                    |             |
|             | size                    |             |
|             | sort                    |             |
| basic       | sort_complex            |             |
|             | spacing                 |             |
| shape       | split                   |             |
|             | sqrt                    |             |
|             | square                  |             |
|             | squeeze                 |             |
|             | stack                   |             |
|             | std                     |             |
|             | str_                    |             |
|             | strings                 |             |
|             | subtract                |             |
|             | sum                     |             |
|             | swapaxes                |             |
|             | take                    |             |
|             | take_along_axis         |             |
|             | tan                     |             |
|             | tanh                    |             |
| op 2 arrays | tensordot               |             |
|             | test                    |             |
|             | testing                 |             |
| shape       | tile                    |             |
|             | timedelta64             |             |
|             | trace                   |             |
|             | transpose               |             |
|             | trapezoid               |             |
| basic       | trapz                   |             |
| 2d          | tri                     |             |
|             | tril                    |             |
|             | tril_indices            |             |
|             | tril_indices_from       |             |
| basic       | trim_zeros              |             |
| 2d          | triu                    |             |
|             | triu_indices            |             |
|             | triu_indices_from       |             |
|             | true_divide             |             |
|             | trunc                   |             |
|             | typecodes               |             |
|             | typename                |             |
|             | typing                  |             |
|             | ubyte                   |             |
|             | ufunc                   |             |
|             | uint                    |             |
|             | uint16                  |             |
|             | uint32                  |             |
|             | uint64                  |             |
|             | uint8                   |             |
|             | uintc                   |             |
|             | uintp                   |             |
|             | ulong                   |             |
|             | ulonglong               |             |
| set         | union1d                 |             |
| basic       | unique                  |             |
|             | unique_all              |             |
|             | unique_counts           |             |
|             | unique_inverse          |             |
|             | unique_values           |             |
|             | unpackbits              |             |
| indexing    | unravel_index           |             |
|             | unsignedinteger         |             |
|             | unstack                 |             |
| basic       | unwrap                  |             |
|             | ushort                  |             |
| 2d          | vander                  |             |
|             | var                     |             |
| op 2 arrays | vdot                    |             |
|             | vecdot                  |             |
|             | vecmat                  |             |
| basic       | vectorize               |             |
|             | void                    |             |
| shape       | vsplit                  |             |
| shape       | vstack                  |             |
| create      | where                   |             |
| create      | zeros                   |             |
| create      | zeros_like              |             |

# `ndarray`
* https://numpy.org/doc/stable/reference/arrays.html

* Attributes: `attr`

* Methods
** array creation
** shape manipulation: `shape`
** item selection and manipulation: `item`
** calculation: `calculation`

* Arithmetic, matrix multiplication, and comparison operations
** comparison operator
** truth value of array
** unary operator
** arithmetic (in-place)
** matrix multiplication

* Special methods: SKIP

## `dir(numpy.ndarray)`

| Category    | Method       | Description |
| :---------- | :----------- | :---------- |
| attr        | T            |             |
| calculation | all          |             |
| calculation | any          |             |
| calculation | argmax       |             |
| calculation | argmin       |             |
|             | argpartition |             |
| item        | argsort      |             |
| convetsion  | astype       |             |
| attr        | base         |             |
| convetsion  | byteswap     |             |
| item        | choose       |             |
| calculation | clip         |             |
| item        | compress     |             |
| calculation | conj         |             |
|             | conjugate    |             |
| convetsion  | copy         |             |
| attr        | ctypes       |             |
| calculation | cumprod      |             |
| calculation | cumsum       |             |
| attr        | data         |             |
|             | device       |             |
| item        | diagonal     |             |
| op 2 arrays | dot          |             |
| attr        | dtype        |             |
| convetsion  | dump         |             |
| convetsion  | dumps        |             |
| convetsion  | fill         |             |
| attr        | flags        |             |
| attr        | flat         |             |
| shape       | flatten      |             |
| convetsion  | getfield     |             |
| attr        | imag         |             |
| convetsion  | item         |             |
| convetsion  | itemset      |             |
| attr        | itemsize     |             |
|             | mT           |             |
| calculation | max          |             |
| calculation | mean         |             |
| calculation | min          |             |
| attr        | nbytes       |             |
| attr        | ndim         |             |
|             | newbyteorder |             |
| item        | nonzero      |             |
|             | partition    |             |
| calculation | prod         |             |
| calculation | ptp          |             |
| item        | put          |             |
| shape       | ravel        |             |
| attr        | real         |             |
| item        | repeat       |             |
| shape       | reshape      |             |
| shape       | resize       |             |
|             | round        |             |
| item        | searchsorted |             |
| convetsion  | setfield     |             |
| convetsion  | setflags     |             |
| attr        | shape        |             |
| attr        | size         |             |
| item        | sort         |             |
| shape       | squeeze      |             |
| calculation | std          |             |
| attr        | strides      |             |
| calculation | sum          |             |
| shape       | swapaxes     |             |
| item        | take         |             |
| convetsion  | to_device    |             |
| convetsion  | tobytes      |             |
| convetsion  | tofile       |             |
| convetsion  | tolist       |             |
| calculation | trace        |             |
| shape       | transpose    |             |
| calculation | var          |             |
| convetsion  | view         |             |

## array indexing

`X[obj]`

- basic slicing: 总是返回视图view
  - `obj`是一个slice对象, 或一个整数, 或一个由slice对象和整数组成的tuple.
  - 可以混杂使用`...`和`newaxis`对象.
  - `obj`是包含slice对象, `...`对象或`newaxis`对象的序列.
  - 例: `X[[1,2,slice(None)]]`, `X[(1,2,3)]`/`X[1,2,3]`
- advanced indexing: 总是返回拷贝copy
  - `obj`是一个非tuple的序列对象, 或一个`ndarray`(元素数据类型为整数或布尔型), 或一个至少有一个序列对象或`ndarray`(元素数据类型为整数或布尔型)的tuple.
  - 两种类型: 
    - 整数.
    - 布尔型: `obj`是元素类型为布尔型的`ndarray`.
  - 例: `X[(1,2,3),]`, `X[[1,2,3]]`

# `ufunc`
* https://numpy.org/doc/stable/reference/ufuncs.html

perform element-by-element operations over an array or a set of arrays.

* math operations
* trigonometric functions
* bit-twiddling functions
* comparison functions
* floating functions

## Broadcasting
* [Explanations - Broadcasting](https://numpy.org/doc/stable/user/basics.broadcasting.html)

ufunc在处理不同形状shape的数组时:
- 规则1: 数组有不同的维度dimension时, 重复的将1前向追加prepend到较小维度数组的形状前, 直到两个数组有同样的维度.
- 规则2: 数组在一个维度大小为1时, 表现的像在那个维度有最大的大小.

示例:
- A 4 x 6 x 5, B 4 x 6 x 1: B[..., k] = B[..., 0] k = 1,2,3,4
- A 4 x 6 x 5, B 5: B as 1 x 1 x 5, then broadcast to 4 x 6 x 5


# Modules

main
- `numpy`: Routines and objects
- `numpy.exceptions`: General exceptions used by NumPy.
- `numpy.fft`: discrete Fourier transform
- `numpy.linalg`: linear algebra
- `numpy.polynomial`: A sub-package for efficiently dealing with polynomials
- `numpy.random`: random numbers
- `numpy.strings`: ufuncs on arrays of `numpy.str_`, `numpy.bytes_`
- `numpy.testing`: Common test support for all numpy test scripts
- `numpy.typing`: `ArrayLike`, `DTypeLike`

special-purpose
- `numpy.ctypeslib`: interacting with NumPy objects with ctypes
- `numpy.dtypes`: dtype classes (typically not used directly by end users)
- `numpy.emath`: mathematical functions with automatic domain
- `numpy.lib`: utilities & functionality which do not fit the main namespace
- `numpy.rec`: record arrays (largely superseded by dataframe libraries)

leagacy
- `numpy.char`: legacy string functionality, only for fixed-width strings
- `numpy.f2py`: Fortran binding generation (usually used from the command line only)
- `numpy.ma`: masked arrays (not very reliable, needs an overhaul)

deprecated
- `numpy.core`: The `numpy.core` submodule exists solely for backward compatibility purposes. The original `core` was renamed to `_core` and made private. `numpy.core` will be removed in the future.
- `numpy.distutils`: build system support
- `numpy.matlib`: functions supporting matrix instances


# `numpy.char`

character array

# `numpy.core`


# `numpy.ctypeslib`
# `numpy.dtypes`
* https://numpy.org/doc/stable/reference/arrays.dtypes.html

```python
# Create a data type object.
dtype(dtype-param[, align, copy])
```

What can be converted to a data-type object is described below: `dtype-param`
- `dtype` object
- `None`: `float64`
- array scalar type
- generic types
- built-in Python types: `int`, `bool`, `float`, `complex`, `bytes`, `str`, `memoryview`, all others
- types with `.dtype`
- one-character string: character code, ex `b`, `>H`
Several kinds of strings can be converted. Recognized strings can be prepended with `'>'` (big-endian), `'<'` (little-endian), or `'='` (hardware-native, the default), to specify the byte order.
- Array-protocol type strings: ex `i4,` `f8`
- String with comma-separated fields, ex:
  - `i4, (2,3)f8, f4`: a 32-bit integer, 2 x 3 sub-array of 64-bit float, 32-bit float
- Type strings: Any string name of a NumPy dtype, ex `uint32`, `float64`
- `(flexible_dtype, itemsize)`                               - WTF!!!
- `(fixed_dtype, shape)`
- `[(field_name, field_dtype, field_shape), ...]`
- `{'names': ..., 'formats': ..., 'offsets': ..., 'titles': ..., 'itemsize': ...}`
- `{'field1': ..., 'field2': ..., ...}`
- `(base_dtype, new_dtype)`


array scalar type

![](https://numpy.org/doc/stable/_images/dtype-hierarchy.png)

| type          | Python dual          | character code | alias                      | description    |
| :------------ | :------------------- | :------------- | :------------------------- | :------------- |
| `byte`        |                      | `'b'`          | `int8`                     | signed         |
| `short`       |                      | `'h'`          | `int16`                    | signed         |
| `intc`        |                      | `'i'`          | `int32`                    | signed         |
| `int_`        | `int`                | `'l'`          | `int64`, `intp`(`'p'`)     | signed         |
| `long`        |                      |                | `int_`                     | signed         |
| `longlong`    |                      | `'q'`          |                            | signed         |
| `ubyte`       |                      | `'B'`          | `uint8`                    | unsigned       |
| `ushort`      |                      | `'H'`          | `uint16`                   | unsigned       |
| `uintc`       |                      | `'I'`          | `uint32`                   | unsigned       |
| `uint`        |                      | `'L'`          | `uint64`, `unitp`(`'N'`)   | unsigned       |
| `ulong`       |                      |                | `uint`                     | unsigned       |
| `ulonglong`   |                      | `'Q'`          |                            | unsigned       |
| `half`        |                      | `'e'`          | `float16`                  | float          |
| `single`      |                      | `'f'`          | `float32`                  | float          |
| `double`      | `float`              | `'d'`          | `float64`                  | float          |
| `longdouble`  |                      | `'g'`          | `float96`, `float128`      | float          |
| `csingle`     |                      | `'F'`          | `complex64`                | complex float  |
| `cdouble`     | `complex`            | `'D'`          | `complex128`               | complex float  |
| `clongdouble` |                      | `'G'`          | `complex192`, `complex256` | complex float  |
| `bool`        |                      | `'?'`          |                            | boolean        |
| `bool_`       | `bool`               |                | `bool`                     | boolean        |
| `datetime64`  | `datetime.datetime`  | `'M'`          |                            |                |
| `timedelta64` | `datetime.timedelta` | `'m'`          |                            |                |
| `object_`     |                      | `'O'`          |                            | Python object  |
| `bytes_`      | `bytes`              | `'S'`          |                            | byte string    |
| `str_`        | `str`                | `'U'`          |                            | unicode string |
| `void`        |                      | `'V'`          |                            |                |

Array-protocol type strings:

| type string  | Description                             |
| ------------ | --------------------------------------- |
| `'?'`        | boolean                                 |
| `'b'`        | (signed) byte                           |
| `'B'`        | unsigned byte                           |
| `'i'`        | (signed) integer                        |
| `'u'`        | unsigned integer                        |
| `'f'`        | floating-point                          |
| `'c'`        | complex-floating point                  |
| `'m'`        | timedelta                               |
| `'M'`        | datetime                                |
| `'O'`        | (Python) objects                        |
| `'S'`, `'a'` | zero-terminated bytes (not recommended) |
| `'U'`        | Unicode string                          |
| `'V'`        | raw data (`void`)                       |

# `numpy.exceptions`
# `numpy.f2py`
# `numpy.fft`
# `numpy.lib`
# `numpy.linalg`

* `@` operator
* matrix and vector product
* decompositions
* matrix eigenvalues
* norms
* inverting matrix

# `numpy.ma`

Masked Arrays

# `numpy.matlib`

# `numpy.polynomial`

# `numpy.random`

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

# `numpy.rec`

record array

# `numpy.strings`

# `numpy.test`

# `numpy.testing`

# `numpy.typing`

# FAQ
* [convert string representation of array to numpy array in python](https://stackoverflow.com/questions/38886641/convert-string-representation-of-array-to-numpy-array-in-python)
```python
s = '[0 1 2 3]'
a = np.fromstring(s[1:-1], dtype=np.int, sep=' ')
print(a) # [0 1 2 3]
```

# See Also

* [Numba](./Numba.md)

