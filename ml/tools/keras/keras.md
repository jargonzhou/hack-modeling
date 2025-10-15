# Keras
* https://keras.io/
* code: https://github.com/keras-team

> A superpower for ML developers
>
> Keras is a deep learning API designed for human beings, not machines. Keras focuses on debugging speed, code elegance & conciseness, maintainability, and deployability. When you choose Keras, your codebase is smaller, more readable, easier to iterate on.
>
> Keras is a deep learning API written in Python and capable of running on top of either *JAX*, *TensorFlow*, or *PyTorch*. - [About](https://keras.io/getting_started/about/)

Keras 3 is available on PyPI as `keras`. Note that Keras 2 remains available as the `tf-keras` package.

# Concepts

> Deep Learning with Python - 3.6 Anatomy of a neural network: Understanding core Keras APIs

- Layers: the building blocks of deep learning
- from layers to models
- the compile step: configuring the learning process
  - loss functions
  - optimizer
  - metrics
- picking a loss function
- understanding the `fit()` method
- monitoring loss and metrics on validation data
- inference: using a model after training


> Deep Learning with Python - 5. Fundamentals of machine learning

maximize generalization, prevent overfitting
- get more training data, or better training data.
- develop better features.
- reduce the capacity of the model.
- add weight regularization (for smaller models).
-add dropout.

> Deep Learning with Python - 6. The universal workflow of machine learning

- define the task
  - frame the problem
  - collect a dataset
  - understand your data
  - choose a measure of success
- develop a model
  - prepare the data
  - choose an evaluation protocol
  - beat a baseline
  - scale up: develop a model that overfits
  - regularize and tune your model
- deploy the model
  - explan your work to stakeholders and set expectations
  - ship an inference model
  - monitro your model in the wild
  - maintain your model

> Deep Learning with Python - 7. Working with Keras: A deep dive

- Different ways to build Keras models
  - The Sequential model
  - The Functional API
  - Model subclassing
  - all models in the Keras API can smoothly interoperate with each other.
- Using built-in training and evaluation loops
  - provide your own custom metrics
  - pass callbacks to `fit()` to schedule actions to be taken at specific points during training
  - monitoring and virualization with TensorBoard 
- Writing your own training and evaluation loops
  - `predictions = model(inputs)`
  - `gradients = tape.gradients(loss, model.trainable_weights)`
  - `@tf.function`
  - `Model`: `train_step()`, `metrics()`
    - `compiled_loss`, `compiled_metrics`, `metrics`

# API
* https://keras.io/api/
## Models API

concepts
- the model class
- the sequential class
- model training APIs
- saving & serialization

### The Sequence API

```python
model = tf.keras.Sequential()
model.add(...)
model = tf.keras.Sequential([...])

model.summary()
model.layers
model.get_layer('...')
model.layers[0].get_weights()

model.compile(loss="...", optimizer="...", metrics=["..."])
history = model.fit(X_train, y_train, epochs=..., validation_data=(X_valid, y_valid))
model.evaluate(X_test, y_test)
y_proba = model.predict(X_new)

# save model: tf, h5
model.save("my_keras_model", save_format="tf")
# load model
load_model("my_keras_model")

# save/load weights
save_weights()
load_weights()
```

### The Functional API
* https://keras.io/guides/functional_api/

The Keras functional API is a way to create models that are more flexible than the `keras.Sequential` API. The functional API can handle models with non-linear topology, shared layers, and even multiple inputs or outputs.
The main idea is that a deep learning model is usually a directed acyclic graph (DAG) of layers. So the functional API is a way to **build graphs of layers**.

```python
normalization_layer = tf.keras.layers.Normalization()
...
input_ = tf.keras.layers.Input(shape=X_train.shape[1:])
# layer as functions
normalized = normalization_layer(input_)
...
output = output_layer(concat)
model = tf.keras.Model(inputs=[input_], outputs=[output])
```

### The Subclassing API
* [Making new layers and models via subclassing](https://keras.io/guides/making_new_layers_and_models_via_subclassing/)

One of the central abstractions in Keras is the `Layer` class. A layer encapsulates both 
- a **state** (the layer's "weights"): `__init__()`, and 
- a **transformation** from inputs to outputs (a "call", the layer's forward pass): `call(self, inputs)`.

## Layers API

concepts
- the base layer class `Layer`
	- `weights`
	- `trainable_weights`
	- `non_trainable_weights`
	- `add_weight()`
	- `trainable`
	- `get_weights()`
	- `set_weights()`
	- `get_config()`
	- `add_loss()`
	- `losses`
- layer activations
- layer weight initializers: `kernel_initializer`, `bias_initializer`
	- `RandomNormal`
	- `RandomUniform`
	- `TruncatedNormal`
	- `Zeros`
	- `Ones`
	- `GlorotNormal`
	- `GlorotUniform`
	- `HeNormal`
	- `HeUniform`
	- `Orthogonal`
	- `Constant`
	- `VarianceScaling`
	- `LecunNormal`
	- `LecunUniform`
	- `IdentityInitializer`
- layer weight regularizers
	- `Regularizer`
	- `L1`
	- `L2`
	- `L1L2`
	- `OrthogonalRegularizer`
- layer weight constraints
	- `Constraint`
	- `MaxNorm`
	- `MinMaxNorm`
	- `NonNeg`
	- `UnitNorm`
- core layers
	- `Input`
	- `InputSpec`
	- `Dense`
	- `EinsumDense`
	- `Activation`
	- `Embedding`
	- `Masking`
	- `Lambda`
	- `Identity`
- convolution layers
	- `Conv1D`
	- `Conv2D`
	- `Conv3D`
	- `SeparableConv1D`
	- `SeparableConv2D`
	- `DepthwiseConv1D`
	- `DepthwiseConv2D`
	- `Conv1DTranspose`
	- `Conv2DTranspose`
	- `Conv3DTranspose`
- pooling layers
	- `MaxPooling1D`
	- `MaxPooling2D`
	- `MaxPooling3D`
	- `AveragePooling1D`
	- `AveragePooling2D`
	- `AveragePooling3D`
	- `GlobalMaxPooling1D`
	- `GlobalMaxPooling2D`
	- `GlobalMaxPooling3D`
	- `GlobalAveragePooling1D`
	- `GlobalAveragePooling2D`
	- `GlobalAveragePooling3D`
- recurrent layers
	- `LSTM`
	- `LSTM cell`
	- `GRU`
	- `GRU Cell`
	- `SimpleRNN`
	- `TimeDistributed`
	- `Bidirectional`
	- `ConvLSTM1D`
	- `ConvLSTM2D`
	- `ConvLSTM3D`
	- `Base RNN`
	- `Simple RNN cell`
	- `Stacked RNN cell`
- preprocessing layers
	- Text preprocessing
	- Numerical features preprocessing layers
	- Categorical features preprocessing layers
	- Image preprocessing layers
	- Image augmentation layers
	- Audio preprocessing layers
- normalization layers: `adapt()`
	- `BatchNormalization`
	- `LayerNormalization`
	- `UnitNormalization`
	- `GroupNormalization`
- regularization layers
	- `Dropout`
	- `SpatialDropout1D`
	- `SpatialDropout2D`
	- `SpatialDropout3D`
	- `GaussianDropout`
	- `AlphaDropout`
	- `GaussianNoise`
	- `ActivityRegularization`
- attention layers
  - `GroupQueryAttention`
	- `MultiHeadAttention`
	- `Attention`
	- `AdditiveAttention`
- reshaping layers
	- `Reshape`
	- `Flatten`
	- `RepeatVector`
	- `Permute`
	- `Cropping1D`
	- `Cropping2D`
	- `Cropping3D`
	- `UpSampling1D`
	- `UpSampling2D`
	- `UpSampling3D`
	- `ZeroPadding1D`
	- `ZeroPadding2D`
	- `ZeroPadding3D`
- merging layers
	- `Concatenate`
	- `Average`
	- `Maximum`
	- `Minimum`
	- `Add`
	- `Subtract`
	- `Multiply`
	- `Dot`
- activation layers
	- `ReLU`
	- `Softmax`
	- `LeakyReLU`
	- `PReLU`
	- `ELU`
- backend-specific layers
	- `TorchModuleWrapper`
	- `Tensorflow SavedModel`
  - `JaxLayer`
  - `FlaxLayer`

| Actication Function | Description |
| :------------------ | :---------- |
| celu                |             |
| elu                 |             |
| exponential         |             |
| gelu                |             |
| glu                 |             |
| hard_shrink         |             |
| hard_sigmoid        |             |
| hard_silu           |             |
| hard_tanh           |             |
| leaky_relu          |             |
| linear              |             |
| log_sigmoid         |             |
| log_softmax         |             |
| mish                |             |
| relu                |             |
| relu6               |             |
| selu                |             |
| sigmoid             |             |
| silu                |             |
| softmax             |             |
| soft_shrink         |             |
| softplus            |             |
| softsign            |             |
| sparse_plus         |             |
| sparsemax           |             |
| squareplus          |             |
| tanh                |             |
| tanh_shrink         |             |
| threshold           |             |

## Callbacks API

A **callback** is an object that can perform actions at various stages of training (e.g. at the start or end of an epoch, before or after a single batch, etc).

concepts
- Base `Callback` class
- `ModelCheckpoint`
- `BackupAndRestore`
- `TensorBoard`
- `EarlyStopping`
- `LearningRateScheduler`
- `ReduceLROnPlateau`
- `RemoteMonitor`
- `LambdaCallback`
- `TerminateOnNaN`
- `CSVLogger`
- `ProgbarLogger`
- `SwapEMAWeights`

```python
checkpoint_cb = tf.keras.callbacks.ModelCheckpoint("my_checkpoints", save_weights_only=True)
history = model.fit([...], callbacks=[checkpoint_cb])
```

```python
on_epoch_begin(epoch, logs) # Called at the start of every epoch
on_epoch_end(epoch, logs)   # Called at the end of every epoch
on_batch_begin(batch, logs) # Called right before processing each batch
on_batch_end(batch, logs)   # Called right after processing each batch
on_train_begin(logs)        # Called at the start of training
on_train_end(logs)          # Called at the end of training
```

## Ops API

concepts
- NumPy ops
- NN ops
- Linear algebra ops
- Core ops
- Image ops
- FFT ops

## Optimizers

optimizers
- `SGD`
- `RMSprop`
- `Adam`
- `AdamW`
- `Adadelta`
- `Adagrad`
- `Adamax`
- `Adafactor`
- `Nadam`
- `Ftrl`
- `Lion`
- `Lamb`
- `LossScaleOptimizer`
- Learning rate schedules API
	- `LearningRateSchedule`
	- `ExponentialDecay`
	- `PiecewiseConstantDecay`
	- `PolynomialDecay`
	- `InverseTimeDecay`
	- `CosineDecay`
	- `CosineDecayRestarts`
- `Muon`

```python
optimizer=tf.keras.optimizers.SGD()
```



## Metrics

metrics
- Base Metric class
- Accuracy metrics
	- `Accuracy`
	- `BinaryAccuracy`
	- `CategoricalAccuracy`
	- `SparseCategoricalAccuracy`
	- `TopKCategoricalAccuracy`
	- `SparseTopKCategoricalAccuracy`
- Probabilistic metrics
	- `BinaryCrossentropy`
	- `CategoricalCrossentropy`
	- `SparseCategoricalCrossentropy`
	- `KLDivergence`
	- `Poisson`
- Regression metrics
	- `MeanSquaredError`
	- `RootMeanSquaredError`
	- `MeanAbsoluteError`
	- `MeanAbsolutePercentageError`
	- `MeanSquaredLogarithmicError`
	- `CosineSimilarity`
	- `LogCoshError`
	- `R2Score`
- Classification metrics based on True/False positives & negatives
	- `AUC`
	- `Precision`
	- `Recall`
	- `TruePositives`
	- `TrueNegatives`
	- `FalsePositives`
	- `FalseNegatives`
	- `PrecisionAtRecall`
	- `RecallAtPrecision`
	- `SensitivityAtSpecificity`
	- `SpecificityAtSensitivity`
	- `F1Score`
	- `FBetaScore`
- Image segmentation metrics
	- `IoU`
	- `BinaryIoU`
	- `OneHotIoU`
	- `OneHotMeanIoU`
	- `MeanIoU`
- Hinge metrics for "maximum-margin" classification
	- `Hinge`
	- `SquaredHinge`
	- `CategoricalHinge`
- Metric wrappers and reduction metrics
	- `MeanMetricWrapper`
	- `Mean`
	- `Sum`

```python
metrics=[tf.keras.metrics.sparse_categorical_accuracy]
```

## Losses

- Probabilistic losses
	- `BinaryCrossentropy`
	- `BinaryFocalCrossentropy`
	- `CategoricalCrossentropy`
	- `CategoricalFocalCrossentropy`
	- `SparseCategoricalCrossentropy`
	- `Poisson`
	- `CTC`
	- `KLDivergence`
	- `binary_crossentropy()`
	- `categorical_crossentropy()`
	- `sparse_categorical_crossentropy()`
	- `poisson()`
	- `ctc()`
	- `kl_divergence()`
- Regression losses
	- `MeanSquaredError`
	- `MeanAbsoluteError`
	- `MeanAbsolutePercentageError`
	- `MeanSquaredLogarithmicError`
	- `CosineSimilarity`
	- `Huber`
	- `LogCosh`
	- `Tversky`
	- `Dice`
	- `mean_squared_error()`
	- `mean_absolute_error()`
	- `mean_absolute_percentage_error()`
	- `mean_squared_logarithmic_error()`
	- `cosine_similarity()`
	- `huber()`
	- `log_cosh()`
	- `tversky()`
	- `dice()`
- Hinge losses for "maximum-margin" classification
	- `Hinge`
	- `SquaredHinge`
	- `CategoricalHinge`
	- `hinge()`
	- `squared_hinge()`
	- `categorical_hinge()`

```python
loss=tf.keras.losses.sparse_categorical_crossentropy
```

## Data loading
## Built-in small datasets

- MNIST digits classification dataset
- CIFAR10 small images classification dataset
- CIFAR100 small images classification dataset
- IMDB movie review sentiment classification dataset
- Reuters newswire classification dataset
- Fashion MNIST dataset, an alternative to MNIST
- California Housing price regression dataset



## Keras Applications
## Mixed precision
## Multi-device distribution
## RNG API
## Rematerialization
## Utilities

# KerasTuner
* https://keras.io/keras_tuner/

KerasTuner is an easy-to-use, scalable **hyperparameter optimization framework** that solves the pain points of hyperparameter search. Easily configure your search space with a define-by-run syntax, then leverage one of the available search algorithms to find the best hyperparameter values for your models. KerasTuner comes with Bayesian Optimization, Hyperband, and Random Search algorithms built-in, and is also designed to be easy for researchers to extend in order to experiment with new search algorithms.

concepts
- Tune the model architecture: function with argument `HyperParameters` to return a model
  - `Tuner`: `RandomSearch`, `BayesianOptimization`, `Hyperband`
- Tune model training: subclass `HyperModel`
- Tune data preprocessing: `keras.layers.Normalization`
- Specify the tuning objective: use Keras metrics
- Tune end-to-end workflows: override `Tuner.run_trial()`
- pre-made tunable applications: `HyperResNet` and `HyperXception`

```python
import keras_tuner as kt
```

# Keras Recommenders
* https://keras.io/keras_rs/

Keras Recommenders is a library for building recommender systems on top of Keras 3. Keras Recommenders works natively with TensorFlow, JAX, or PyTorch. It provides a collection of building blocks which help with the full workflow of creating a recommender system. As it's built on Keras 3, models can be trained and serialized in any framework and re-used in another without costly migrations.

# KerasHub
* https://keras.io/keras_hub/

KerasHub is a pretrained modeling library that aims to be simple, flexible, and fast. The library provides Keras 3 implementations of popular model architectures, paired with a collection of pretrained checkpoints available on Kaggle Models. Models can be used for both training and inference, on any of the TensorFlow, Jax, and Torch backends.
