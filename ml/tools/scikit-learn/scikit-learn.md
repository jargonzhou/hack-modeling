# scikit-learn
* https://scikit-learn.org/
* [Glossary of Common Terms and API Elements](https://scikit-learn.org/stable/glossary.html)

> Machine Learning in Python
> 
> * Simple and efficient tools for predictive data analysis
> * Accessible to everybody, and reusable in various contexts
> * Built on NumPy, SciPy, and matplotlib
> * Open source, commercially usable - BSD license

# Concepts

> TODO: from 'User Guide'

1. Supervised learning
2. Unsupervised learning
3. Model selection and evaluation
4. Metadata Routing
5. Inspection
6. Visualizations
7. Dataset transformations
8. Dataset loading utilities
9. Computing with scikit-learn
10. Model persistence
11. Common pitfalls and recommended practices
12. Dispatching
13. Choosing the right estimator

## API Design
* [API design for machine learning software: experiences from the scikit-learn project](https://arxiv.org/abs/1309.0238): 2013

all objects share a consistent and simple interface:
- **estimators**: any object that can estimate some parameters based on a dataset.
  - ex: `SimpleImputer`
  - performed by `fit()`
  - hyperparameters: parameters except dataset parameter, to guide the estimation process
    - ex: `SimpleImputer.strategy`
  - learned parameters
    - ex: `imputer.statistics_` 
- **transformers**: transform a dataset.
  - ex: `SimpleImputer`, some estimators can also transform a dataset.
  - performed by `transform()`, `fit_transform()`
  - output NumPy arrays
- **predictors**: given a dataset, make predictions.
  - ex: `LinearRegression`
  - `predict()`, `score()`

advanced API:
- meta-estimators: take a base estimator as input, use it internally for learning and make predicitons.
  - ex: `OneVsOneClassfifier`
- `Pipeline`: chain multiple estimators into a single one.
- `FeatureUnion`: combine multiple transformers into a single one that concatenates their outputs.
- model seletion: the best combination of hyperparameters with respect to user-specified criterion.
  - `GridSearchCV`, `RandomizedSearchCV`
  - cross-valitation scheme: k-fold, stratified k-fold, leave-one-out
  - score function: estimator's `score()`, accuracy, AUC, $F_{1}$, $R^{2}$, mean squared error.

| Package                         | Description                                                                       |
| :------------------------------ | :-------------------------------------------------------------------------------- |
| `sklearn`                       | Configure global settings and get information about the working environment.      |
| `sklearn.base`                  | Base classes for all estimators and various utility functions.                    |
| `sklearn.calibration`           | Methods for calibrating predicted probabilities.                                  |
| `sklearn.cluster`               | Popular unsupervised clustering algorithms.                                       |
| `sklearn.compose`               | Meta-estimators for building composite models with transformers.                  |
| `sklearn.covariance`            | Methods and algorithms to robustly estimate covariance.                           |
| `sklearn.cross_decomposition`   | Algorithms for cross decomposition.                                               |
| `sklearn.datasets`              | Utilities to load popular datasets and artificial data generators.                |
| `sklearn.decomposition`         | Matrix decomposition algorithms.                                                  |
| `sklearn.discriminant_analysis` | Linear and quadratic discriminant analysis.                                       |
| `sklearn.dummy`                 | Dummy estimators that implement simple rules of thumb.                            |
| `sklearn.ensemble`              | Ensemble-based methods for classification, regression and anomaly detection.      |
| `sklearn.exceptions`            | Custom warnings and errors used across scikit-learn.                              |
| `sklearn.experimental`          | Importable modules that enable the use of experimental features or estimators.    |
| `sklearn.feature_extraction`    | Feature extraction from raw data.                                                 |
| `sklearn.feature_selection`     | Feature selection algorithms.                                                     |
| `sklearn.frozen`                | Estimator that wraps a fitted estimator to prevent re-fitting.                    |
| `sklearn.gaussian_process`      | Gaussian process based regression and classification.                             |
| `sklearn.impute`                | Transformers for missing value imputation.                                        |
| `sklearn.inspection`            | Tools for model inspection.                                                       |
| `sklearn.isotonic`              | Isotonic regression for obtaining monotonic fit to data.                          |
| `sklearn.kernel_approximation`  | Approximate kernel feature maps based on Fourier transforms and count sketches.   |
| `sklearn.kernel_ridge`          | Kernel ridge regression.                                                          |
| `sklearn.linear_model`          | A variety of linear models.                                                       |
| `sklearn.manifold`              | Data embedding techniques.                                                        |
| `sklearn.metrics`               | Score functions, performance metrics, pairwise metrics and distance computations. |
| `sklearn.mixture`               | Mixture modeling algorithms.                                                      |
| `sklearn.model_selection`       | Tools for model selection, such as cross validation and hyper-parameter tuning.   |
| `sklearn.multiclass`            | Multiclass learning algorithms.                                                   |
| `sklearn.multioutput`           | Multioutput regression and classification.                                        |
| `sklearn.naive_bayes`           | Naive Bayes algorithms.                                                           |
| `sklearn.neighbors`             | The k-nearest neighbors algorithms.                                               |
| `sklearn.neural_network`        | Models based on neural networks.                                                  |
| `sklearn.pipeline`              | Utilities to build a composite estimator as a chain of transforms and estimators. |
| `sklearn.preprocessing`         | Methods for scaling, centering, normalization, binarization, and more.            |
| `sklearn.random_projection`     | Random projection transformers.                                                   |
| `sklearn.semi_supervised`       | Semi-supervised learning algorithms.                                              |
| `sklearn.svm`                   | Support vector machine algorithms.                                                |
| `sklearn.tree`                  | Decision tree based models for classification and regression.                     |
| `sklearn.utils`                 | Various utilities to help with development.                                       |

```python
from sklearn.impute import SimpleImputer

from sklearn.pipeline import Pipeline
from sklearn.pipeline import make_pipeline

from sklearn.compose import ColumnTransformer
from sklearn.compose import make_column_selector, make_column_transformer

from sklearn.metrics import mean_squared_error
```

# Classification
Identifying which category an object belongs to.

# Regression
Predicting a continuous-valued attribute associated with an object.

```python
from sklearn.linear_model import LinearRegression
from sklearn.tree import DecisionTreeRegressor
from sklearn.ensemble import RandomForestRegressor
```

# Clustering
Automatic grouping of similar objects into sets.

```python
from sklearn.cluster import KMeans
```

# Dimensionality reduction
Reducing the number of random variables to consider.

# Model selection
Comparing, validating and choosing parameters and models.

```python
from sklearn.model_selection import train_test_split

from sklearn.model_selection import StratifiedShuffleSplit

from sklearn.model_selection import cross_val_score

from sklearn.model_selection import GridSearchCV, RandomizedSearchCV
```

# Preprocessing
Feature extraction and normalization.


```python
from sklearn.preprocessing import OrdinalEncoder
from sklearn.preprocessing import OneHotEncoder

from sklearn.preprocessing import MinMaxScaler
from sklearn.preprocessing import StandardScaler

from sklearn.preprocessing import FunctionTransformer
```

# Dataset
* [7. Dataset transformations](https://scikit-learn.org/stable/data_transforms.html)

* [8. Dataset loading utilities](https://scikit-learn.org/stable/datasets.html): 
  - dataset loader: Toy datasets - `Bunch`
    - example: `load_digits()`: load a copy of the test set of the UCI ML hand-written digits datasets - see [Data Visualization in ML Workflow](../matplotlib/matplotlib.ipynb)
  - dataset fetcher: Real world datasets - `Bunch`
    - example: `fetch_openml()`: Downloading datasets from the [openml.org](https://openml.org/) repository
  - dataset generation functions: Generated datasets `(X, y)`
    - generators for classification, clustering, regression, manifold learning, decomposition
  - others datasets: sample JPEG images, svmlight/libsvm format, openml.org repositry, external datasets(Numpy array, SciPy sparse matrix)
* API: https://scikit-learn.org/stable/api/sklearn.datasets.html

# FAQ
* [Crafting a minimal reproducer for scikit-learn](https://scikit-learn.org/stable/developers/minimal_reproducer.html)

# See Also
* [SciKeras](https://github.com/adriangb/scikeras): Scikit-Learn API wrapper for Keras.
* [Keras Scikit-Learn API wrappers](https://keras.io/api/utils/sklearn_wrappers/): scikit-learn compatible classifier wrapper for Keras models.