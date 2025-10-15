# Hands-On Machine Learning
* Chollet, Francois. **Deep Learning with Python**. 2021, 2. edition. Manning.
* Géron, Aurélien. **Hands-On Machine Learning with Scikit-Learn, Keras, and TensorFlow: Concepts, Tools, and Techniques to Build Intelligent Systems**. 2022, 3. edition. O’Reilly.
* Ganegedara, Thushan. **TensorFlow in Action**. 2022. Manning.

# Dependencies

| Dependency          | Install                                      | Description                                           |
| :------------------ | :------------------------------------------- | :---------------------------------------------------- |
| Poetry              | `poetry new hands-on-ml`                     | `poetry env activate` `source .venv/Scripts/activate` |
| autopep8            | `poetry add autopep8 --group dev`            |                                                       |
| pylint              | `poetry add pylint --group dev`              |                                                       |
| scikit-learn        | `poetry add scikit-learn`                    |                                                       |
| TensorFlow          | `poetry add tensorflow`                      | `poetry add tensorboard-plugin-profile --group dev`   |
| TensorFlow datasets | `poetry add tensorflow-datasets --group dev` |                                                       |
| Keras               | `poetry add keras`                           |                                                       |
| pydot               | `poetry add pydot --group dev`               |                                                       |
| pandas              | `poetry add pandas`                          | `poetry add pandas-stubs --group dev`                 |
| Matplotlib          | `poetry add matplotlib`                      |                                                       |
| Jupyter             | `poetry add jupyter`                         | Jupyter Notebook, JupyterLab, and the IPython Kernel  |
| Pillow              | `poetry add Pillow`                          |                                                       |

TensorFlow type stubs:
```shell
$ poetry add tensorflow=2.18.0
# version is 2.18.0
$ poetry add types-tensorflow --group dev

# handle: No module named 'tensorflow'
# https://pypi.org/project/tensorflow-intel/
$ poetry add tensorflow-intel=2.18.0

# tensorflow/__init__.py
# Import "distutils" could not be resolved from source Pylance reportMissingModuleSource
# If using Python 3.12 or later, distutils is no longer part of the standard library.
$ poetry add standard-distutils --group dev
```

TensorBoard: 
```shell
$ tensorboard --logdir=./data/tf_logs
# http://localhost:6006
```

# TODO

- can we use Bokeh to interactively visualize the hyperparameter selection effects?
- what does 'Op graph' mean in TensorBoard 'Graphs' panel.