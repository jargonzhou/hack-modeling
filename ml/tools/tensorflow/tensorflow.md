# TensorFlow
* https://www.tensorflow.org/
* code: https://github.com/tensorflow/tensorflow
* forum: https://discuss.ai.google.dev/

> TensorFlow is an end-to-end open source platform for machine learning. It has a comprehensive, flexible ecosystem of tools, libraries, and community resources that lets researchers push the state-of-the-art in ML and developers easily build and deploy ML-powered applications.
>
> TensorFlow was originally developed by researchers and engineers working within the Machine Intelligence team at Google Brain to conduct research in machine learning and neural networks. However, the framework is versatile enough to be used in other areas as well.
> 
> TensorFlow provides stable Python and C++ APIs, as well as a non-guaranteed backward compatible API for other languages.


TODO: https://www.tensorflow.org/tutorials/quickstart/beginner

# Concepts

basics
- end-to-end platform for machine learning:
- multidimensional-array based numeric computation
  - tensors `tf.Tensor`: `tf.constant()`
  - variables `tf.Variable`
- GPU, distributed processing
- automatic differentiation(autodiff): gradient descent
- model construction, training, export
  - graphs, `tf.function`
  - modules `tf.Module`: manage `tf.Variable`, `tf.function`
  - training loop
  - save TF model: checkpointing, SavedModel

Keras

Core APIs

`tf.data`: build input pipelines

accelerators
- distributed training
- GPU
- TPU

Model Garden

Estimators `tf.estimator`
- encapsulate the following actions: Training, Evaluation, Prediction, Export for serving

# Modules

| Module           | Category                     | Description                          |
| :--------------- | :--------------------------- | :----------------------------------- |
| `audio`          | IO, preprocessing            | `tf._api.v2.audio`                   |
| `autodiff`       | Autodiff                     | `tf._api.v2.autodiff` `GradientTape` |
| `autograph`      | Deployment, optimization     | `tf._api.v2.autograph`               |
| `bitwise`        | Mathematics                  | `tf._api.v2.bitwise`                 |
| `compat`         |                              | `tf._api.v2.compat`                  |
| `config`         | Miscellaneous                | `tf._api.v2.config`                  |
| `data`           | IO, preprocessing            | `tf._api.v2.data`                    |
| `debugging`      |                              | `tf._api.v2.debugging`               |
| `distribute`     | Deployment, optimization     | `tf._api.v2.distribute`              |
| `dtypes`         |                              | `tf._api.v2.dtypes`                  |
| `errors`         |                              | `tf._api.v2.errors`                  |
| `experimental`   | Miscellaneous                | `tf._api.v2.experimental`            |
| `feature_column` |                              | `tf._api.v2.feature_column`          |
| `graph_util`     | Deployment, optimization     | `tf._api.v2.graph_util`              |
| `image`          | IO, preprocessing            | `tf._api.v2.image`                   |
| `io`             | IO, preprocessing            | `tf._api.v2.io`                      |
| `keras`          | High-level deep learning API | Keras                                |
| `linalg`         | Mathematics                  | `tf._api.v2.linalg`                  |
| `lite`           | Deployment, optimization     | `tf._api.v2.lite`                    |
| `lookup`         | Sperical data structures     | `tf._api.v2.lookup`                  |
| `math`           | Mathematics                  | `tf._api.v2.math`                    |
| `mlir`           |                              | `tf._api.v2.mlir`                    |
| `nest`           | Sperical data structures     | `tf._api.v2.nest`                    |
| `nn`             | Low-level deep  learning API | `tf._api.v2.nn`                      |
| `profiler`       |                              | `tf._api.v2.profiler`                |
| `quantization`   | Deployment, optimization     | `tf._api.v2.quantization`            |
| `queue`          | IO, preprocessing            | `tf._api.v2.queue`                   |
| `ragged`         | Sperical data structures     | `tf._api.v2.ragged`                  |
| `random`         | Mathematics                  | `tf._api.v2.random`                  |
| `raw_ops`        |                              | `tf._api.v2.raw_ops`                 |
| `saved_model`    | Deployment, optimization     | `tf._api.v2.saved_model`             |
| `sets`           | Sperical data structures     | `tf._api.v2.sets`                    |
| `signal`         | Mathematics                  | `tf._api.v2.signal`                  |
| `sparse`         | Sperical data structures     | `tf._api.v2.sparse`                  |
| `strings`        | Sperical data structures     | `tf._api.v2.strings`                 |
| `summary`        | Visualization                | `tf._api.v2.summary`                 |
| `sysconfig`      |                              | `tf._api.v2.sysconfig`               |
| `test`           |                              | `tf._api.v2.test`                    |
| `tpu`            | Deployment, optimization     | `tf._api.v2.tpu`                     |
| `train`          |                              | `tf._api.v2.train`                   |
| `types`          |                              | `tf._api.v2.types`                   |
| `version`        |                              | `tf._api.v2.version`                 |
| `xla`            | Deployment, optimization     | `tf._api.v2.xla`                     |

- `GradientTape`: Autodiff

# Keras

> Keras 3 will be the default Keras version for TensorFlow 2.16 onwards. - [What's new in TensorFlow 2.16](https://blog.tensorflow.org/2024/03/whats-new-in-tensorflow-216.html)

# Ecosystem

more:
- Learn ML
- Responsible AI
- Recommendation systems

## Models & datasets
* https://www.tensorflow.org/resources/models-datasets

models
- Kaggle Models: A comprehensive repository of trained models ready for fine-tuning and deployable anywhere.
- Model Garden: Machine learning models and examples built with TensorFlow's high-level APIs.
- TensorFlow.js models: Pre-trained machine learning models ready-to-use in the web browser on the client side, or anywhere that JavaScript can run such as Node.js.

datasets
- TensorFlow official datasets: A collection of datasets ready to use with TensorFlow.
  - `tf.data.Datasets`
  - [TFDS](https://www.tensorflow.org/datasets/overview)
    - `pip install tensorflow-datasets`, `import tensorflow_datasets as tfds`
    - [all_datasets](https://www.tensorflow.org/datasets/catalog/overview)
- Google research datasets: Explore large-scale datasets released by Google research teams in a wide range of computer science disciplines.
- Additional dataset resources: Explore other datasets available to use with TensorFlow.

## Tools
* https://www.tensorflow.org/resources/tools

| Tool                  | Description                                                                                                                                                                                                                    |
| :-------------------- | :----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Colab                 | Colaboratory is a free Jupyter notebook environment that requires no setup and runs entirely in the cloud, allowing you to execute TensorFlow code in your browser with a single click.                                        |
| Visual Blocks         | A visual coding web framework to prototype ML workflows using I/O devices, models, data augmentation, and even Colab code as reusable building blocks.                                                                         |
| TensorBoard           | A suite of visualization tools to understand, debug, and optimize TensorFlow programs.                                                                                                                                         |
| What-If Tool          | A tool for code-free probing of machine learning models, useful for model understanding, debugging, and fairness. Available in TensorBoard and jupyter or colab notebooks.                                                     |
| ML Perf               | A broad ML benchmark suite for measuring performance of ML software frameworks, ML hardware accelerators, and ML cloud platforms.                                                                                              |
| XLA                   | XLA (Accelerated Linear Algebra) is a domain-specific compiler for linear algebra that optimizes TensorFlow computations. The results are improvements in speed, memory usage, and portability on server and mobile platforms. |
| TensorFlow Playground | Tinker with a neural network in your browser. Don't worry, you can't break it.                                                                                                                                                 |
| TPU Research Cloud    | The TPU Research Cloud (TRC) program enables researchers to apply for access to a cluster of more than 1,000 Cloud TPUs at no charge to help them accelerate the next wave of research breakthroughs.                          |
| MLIR                  | A new intermediate representation and compiler framework.                                                                                                                                                                      |

### TensorBoard
* https://www.tensorflow.org/tensorboard



## Libraries & extensions
* https://www.tensorflow.org/resources/libraries-extensions

| Libraries & extensions         | Description                                                                                                                                               |
| :----------------------------- | :-------------------------------------------------------------------------------------------------------------------------------------------------------- |
| TensorFlow Addons              | Extra functionality for TensorFlow, maintained by SIG Addons.                                                                                             |
| TensorFlow Agents              | A library for designing, testing, and implementing reinforcement learning algorithms.                                                                     |
| TensorFlow Compression         | A library to build ML models with end-to-end optimized data compression built in.                                                                         |
| TensorFlow Data Validation     | A library to analyze training and serving data to compute descriptive statistics, infer schemas, and detect anomalies.                                    |
| TensorFlow Decision Forests    | State-of-the-art algorithms for training, serving and interpreting models that use decision forests for classification, regression and ranking.           |
| Dopamine                       | A research framework for fast prototyping of reinforcement learning algorithms.                                                                           |
| Fairness Indicators            | A library that enables easy computation of commonly-identified fairness metrics for binary and multiclass classifiers.                                    |
| TensorFlow Federated           | An open source framework for machine learning and other computations on decentralized data.                                                               |
| TensorFlow GNN                 | A library to build neural networks on graph data (nodes and edges with arbitrary features), including tools for preparing input data and training models. |
| TensorFlow Graphics            | A library of computer graphics functionalities ranging from cameras, lights, and materials to renderers.                                                  |
| TensorFlow Hub                 | A library for reusable machine learning. Download and reuse the latest trained models with a minimal amount of code.                                      |
| TensorFlow IO                  | Dataset, streaming, and file system extensions, maintained by SIG IO.                                                                                     |
| TensorFlow JVM                 | Language bindings for Java and other JVM languages, such as Scala or Kotlin.                                                                              |
| KerasCV                        | A library of modular components for common computer vision tasks such as data augmentation, classification, object detection, segmentation, and more.     |
| KerasNLP                       | An easily customizable natural language processing library providing modular components and state-of-the-art preset weights and architectures.            |
| TensorFlow Lattice             | A library for flexible, controlled and interpretable ML solutions with common-sense shape constraints.                                                    |
| TensorFlow Lite Micro          | A library to run ML models on digital signal processors (DSPs), microcontrollers, and other devices with limited memory.                                  |
| TensorFlow Lite Model Maker    | A library that simplifies model training for on-device natural language processing, vision, and audio applications.                                       |
| TensorFlow Lite Support        | A toolkit to customize model interface on Android, create metadata, and build inference pipelines for mobile deployment.                                  |
| TensorFlow Metadata            | Utilities for passing TensorFlow-related metadata between tools.                                                                                          |
| ML Metadata                    | A library for recording and retrieving MLOps metadata associated with machine learning workflows.                                                         |
| TensorFlow Model Analysis      | A library for deep analysis of model results beyond simple training metrics, to measure edge and corner cases and bias.                                   |
| Model Card Toolkit             | A collection of tools to generate documents that provide context and transparency into a model's development and performance.                             |
| Model Optimization Toolkit     | A suite of tools for optimizing ML models for deployment and execution.                                                                                   |
| TensorFlow Model Remediation   | A library to help create and train models in a way that reduces or eliminates user harm resulting from underlying performance biases.                     |
| NdArray                        | Utilities for manipulating data in a n-dimensional space in Java, maintained by SIG JVM.                                                                  |
| Neural Structured Learning     | A learning framework to train neural networks by leveraging structured signals in addition to feature inputs.                                             |
| TensorFlow Privacy             | A Python library that includes implementations of TensorFlow optimizers for training machine learning models with differential privacy.                   |
| TensorFlow Probability         | A library for probabilistic reasoning and statistical analysis.                                                                                           |
| TensorFlow Quantum             | A quantum machine learning library for rapid prototyping of hybrid quantum-classical ML models.                                                           |
| TensorFlow Ranking             | A library for Learning-to-Rank (LTR) techniques on the TensorFlow platform.                                                                               |
| TensorFlow Recommenders        | A library for building recommender system models.                                                                                                         |
| TensorFlow Recommenders Addons | A collection of community projects introducing Dynamic Embedding Technology to large-scale recommendation systems built upon TensorFlow                   |
| TensorFlow Serving             | A flexible, high-performance serving system for machine learning models, designed for production environments                                             |
| Sonnet                         | A library from DeepMind for constructing neural networks.                                                                                                 |
| TensorFlow Text                | A collection of text- and NLP-related classes and ops ready to use with TensorFlow 2.                                                                     |
| TensorFlow Transform           | A library for large-scale feature engineering and eliminating training-serving skew.                                                                      |
| TensorFlow.js                  | A hardware-accelerated library for training and deploying ML models using JavaScript or Node.js.                                                          |
| TFX                            | An end-to-end platform for deploying production ML pipelines.                                                                                             |
| TFX-Addons                     | A collection of community projects to build new components, examples, libraries, and tools for TFX.                                                       |

### TensorFlow.js

### TensorFlow Lite

### TFX

### TensorFlow Hub

# TF-Slim
* https://github.com/google-research/tf-slim

> TF-Slim is a lightweight library for defining, training and evaluating complex models in TensorFlow. Components of tf-slim can be freely mixed with native tensorflow, as well as other frameworks..

# See Also
* [Awesome TensorFlow](https://github.com/jtoy/awesome-tensorflow)
* [Eigen](https://gitlab.com/libeigen/eigen): Eigen is a C++ template library for linear algebra: matrices, vectors, numerical solvers, and related algorithms.
* [NVIDIA cuDNN](https://developer.nvidia.com/cudnn): NVIDIA® CUDA® Deep Neural Network library (cuDNN) is a GPU-accelerated library of primitives for deep neural networks. cuDNN provides highly tuned implementations for standard routines, such as forward and backward convolution, attention, matmul, pooling, and normalization.