# Machine Learning Tools

* [Bokeh](./tools/bokeh/bokeh.md): a Python library for creating interactive visualizations for modern web browsers.
* [Featuretools](https://github.com/alteryx/featuretools): a python library for automated feature engineering.
* [graphviz](https://pypi.org/project/graphviz/): Simple Python interface for Graphviz.
* [JAX](./tools/jax/jax.md): JAX is a Python library for accelerator-oriented array computation and program transformation, designed for high-performance numerical computing and large-scale machine learning.
* [KaTeX](./tools/KaTeX.md)
* [Matplotlib](./tools/matplotlib/matplotlib.md): Visualization with Python.
* [Numba](./tools/numpy/numba.md): A Just-In-Time Compiler for Numerical Functions in Python.
* [NumPy](./tools/numpy/numpy.md): Numerical Python.
* [pandas](./tools/pandas/pandas.md): a fast, powerful, flexible and easy to use open source data analysis and manipulation tool, built on top of the Python programming language.
* [Polars](https://github.com/pola-rs/polars/): an analytical query engine written for DataFrames, written in Rust. Front end in Python | Rust | NodeJS | R | SQL.
* [PyTensor](https://github.com/pymc-devs/pytensor): PyTensor is a Python library that allows one to define, optimize, and efficiently evaluate mathematical expressions involving multi-dimensional arrays. It provides the computational backend for PyMC.
* [R](./tools/R.md)
* [scikit-learn](./tools/scikit-learn/scikit-learn.md): Machine Learning in Python.
* [SciPy](./tools/scipy/scipy.md)
* [seaborn](./tools/matplotlib/seaborn.md): statistical data visualization.
* [statsmodels](./tools/statsmodels/statsmodels.md): a Python module that provides classes and functions for the estimation of many different statistical models, as well as for conducting statistical tests, and statistical data exploration.
* [SymPy](./tools/sympy/sympy.md): a Python library for symbolic mathematics.
* [Theano](https://github.com/Theano/Theano): Theano was a Python library that allows you to define, optimize, and evaluate mathematical expressions involving multi-dimensional arrays efficiently. It is being continued as *PyTensor*.
* [XGBoost](https://github.com/dmlc/xgboost): Scalable, Portable and Distributed Gradient Boosting (GBDT, GBRT or GBM) Library, for Python, R, Java, Scala, C++ and more. Runs on single machine, Hadoop, Spark, Dask, Flink and DataFlow.

# Frameworks
* [Apache MXNet](https://numpy.mxnet.io/): Lightweight, Portable, Flexible Distributed/Mobile Deep Learning with Dynamic, Mutation-aware Dataflow Dep Scheduler; for Python, R, Julia, Scala, Go, Javascript and more. MXNet retired in September 2023 and the move to [the Attic](https://attic.apache.org/projects/mxnet.html) was completed in February 2024.
* [Chainer](https://github.com/chainer/chainer): A deep learning framework. Chainer is under the maintenance phase and further development will be limited to bug-fixes and maintenance only.
* [CoreNLP](https://github.com/stanfordnlp/CoreNLP): A Java suite of core NLP tools for tokenization, sentence segmentation, NER, parsing, coreference, sentiment analysis, etc.
* [DeepLearning4J](https://deeplearning4j.konduit.ai/): Eclipse Deeplearning4j is a suite of tools for running deep learning on the JVM. It's the only framework that allows you to train models from java while interoperating with the python ecosystem through a mix of python execution via our cpython bindings, model import support, and interop of other runtimes such as tensorflow-java and onnxruntime.
* [deepnl](https://github.com/attardi/deepnl): Deep Learning for Natural Language Processing. - 2015
* [DyNet](https://github.com/clab/dynet): The Dynamic Neural Network Toolkit. - 2.1.2 2020-10-21
* [Keras](./tools/keras/keras.md): a deep learning API designed for human beings, not machines.
* [nlpnet](https://github.com/erickrf/nlpnet): A neural network architecture for NLP tasks, using cython for fast performance. Currently, it can perform POS tagging, SRL and dependency parsing.
* [OpenNMT-py](https://github.com/OpenNMT/OpenNMT-py): Open Source Neural Machine Translation and (Large) Language Models in PyTorch.
* [PyTorch](./tools/pytorch/pytorch.md): Tensors and Dynamic neural networks in Python with strong GPU acceleration.
* [spaCy](https://github.com/explosion/spaCy): Industrial-strength Natural Language Processing (NLP) in Python.
* [TensorFlow](./tools/tensorflow/tensorflow.md): an end-to-end open source platform for machine learning.
* [TFLearn](https://github.com/tflearn/tflearn): Deep learning library featuring a higher-level API for TensorFlow. - v0.5.0 2020-11-12
* [Hugging Face](./tools/frameworks/Hugging%20Face.md)
* [Spring AI](./toolsframeworks/Spring%20AI.ipynb)
* [LangChain](./toolsframeworks/LangChain.ipynb)
* [Dify](./toolsframeworks/Dify.ipynb)

# Runtime

* [Google Colab](https://colab.google/): Colab is a hosted Jupyter Notebook service that requires no setup to use and provides free access to computing resources, including GPUs and TPUs. Colab is especially well suited to machine learning, data science, and education.
* [joblib](https://joblib.readthedocs.io/): running Python functions as pipeline jobs.
  * code: https://github.com/joblib/joblib

# Deep Network Graphs
* [Netron](https://github.com/lutzroeder/netron): a viewer for neural network, deep learning and machine learning models.
* [NN-SVG](https://github.com/alexlenail/NN-SVG): Publication-ready NN-architecture schematics.
* [TensorSpace](https://github.com/tensorspace-team/tensorspace): a neural network 3D visualization framework built using TensorFlow.js, Three.js and Tween.js.

# Datasets
* [Project Gutenberg](https://www.gutenberg.org/): Project Gutenberg is a library of over 75,000 free eBooks.

# Miscellaneous
* [Beads](https://github.com/steveyegge/beads): Beads provides a persistent, structured memory for coding agents. It replaces messy markdown plans with a dependency-aware graph, allowing agents to handle long-horizon tasks without losing context.
* [Dolt](https://github.com/dolthub/dolt): Dolt is a SQL database that you can fork, clone, branch, merge, push and pull just like a Git repository.
* [Text-to-SQL/NL2SQL Handbook](https://github.com/HKUSTDial/NL2SQL_Handbook): This is a continuously updated handbook for readers to easily track the latest Text-to-SQL techniques in the literature and provide practical guidance for researchers and practitioners.

# See Also
* [Awesome AI for LAM](https://ai4lam.github.io/awesome-ai4lam/): A curated list of resources, projects, and tools for using Artificial Intelligence in Libraries, Archives, and Museums.
* [Awesome AI Tools](https://github.com/mahseema/awesome-ai-tools): A curated list of Artificial Intelligence Top Tools.

# Internal

* ml_tools
```python
# Usage in notebook:
# common tools
import sys
from pathlib import Path
sys.path.append(Path.cwd().parent.as_posix())
# print(sys.path)

from ml_tools.common import pd_print
```