# Python for Data Analysis

# Dependencies
* Poetry
```shell
$ poetry new python-for-data-analysis
$ poetry env activate
$ source .venv/Scripts/activate
```
* mypy
```shell
$ poetry add mypy --group dev
$ poetry run mypy tests/test_numpy/test_ndarray.py 
```
* numpy
```shell
$ poetry add numpy
```
* matplotlib
```shell
$ poetry add matplotlib
```
* Bokeh
```shell
$ poetry add bokeh
$ bokeh serve --show src/python_for_data_analysis/ex_bokeh/myapp.py
```