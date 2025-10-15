# Python for Data Analysis
* Kazil, Jacqueline / Jarmul, Katharine. **Data Wrangling with Python**. 2016. O’Reilly.
* McKinney, Wes. **Python for Data Analysis: Data Wrangling with pandas, NumPy & Jupyter**. 2022, 3. edition. O’Reilly.
* Oliphant, Travis E. **Guide to NumPy**. 2006.
* Harris, Charles R. / K. Jarrod Millman, et al. **Array programming with NumPy**. 2020. Nature , Vol. 585. p. 357–362.
* Paskhaver, Boris. **Pandas in Action**. 2021. Manning.
* Yim, Aldrin / Chung, Claire / Yu, Allen. **Matplotlib for Python Developers: Effective techniques for data visualization with Python**. 2018, 2. edition. Packt.
* Jolly, Kevin. **Hands-On Data Visualization with Bokeh: Interactive web plotting for Python using Bokeh**. 2018. Packt.
* Varoquaux, Gaël / Gouillart, Emmanuelle / Vahtras, Olaf. **Scipy Lecture Notes**. 2024.

# Dependencies

| Dependency  | Install                               | Description                                           |
| :---------- | :------------------------------------ | :---------------------------------------------------- |
| Poetry      | `poetry new python-for-data-analysis` | `poetry env activate` `source .venv/Scripts/activate` |
| Mypy        | `poetry add mypy --group dev`         | `poetry run mypy tests/test_numpy/test_ndarray.py `   |
| NumPy       | `poetry add numpy`                    |                                                       |
| Matplotlib  | `poetry add matplotlib`               |                                                       |
| Bokeh       | `poetry add bokeh`                    | `bokeh serve --show src/ex_bokeh/myapp.py`            |
| slate3k     | `poetry add slate3k`                  |                                                       |
| xlrd        | `poetry add xlrd`                     |                                                       |
| treelib     | `poetry add treelib`                  |                                                       |
| PrettyTable | `poetry add prettytable`              |                                                       |