# Model Training
* [Exploring Strategies for Training Deep Neural Networks](https://dl.acm.org/doi/10.5555/1577069.1577070) - 2009
* [Understanding the difficulty of training deep feedforward neural networks](https://proceedings.mlr.press/v9/glorot10a/glorot10a.pdf) - 2010
* [A disciplined approach to neural network hyper-parameters: Part 1 -- learning rate, batch size, momentum, and weight decay](https://arxiv.org/abs/1803.09820) - 2018
  * [no part 2](https://forums.fast.ai/t/part-2-for-a-disciplined-approach-to-neural-network-hyper-parameters-part-1/39001/3): see also [EfficientNet: Rethinking Model Scaling for Convolutional Neural Networks](https://arxiv.org/abs/1905.11946), [Designing Network Design Spaces](https://arxiv.org/abs/2003.13678)
* [On Efficient Training of Large-Scale Deep Learning Models: A Literature Review](https://arxiv.org/abs/2304.03589) - 2023
* [Deep Learning Model Training Checklist: Essential Steps for Building and Deploying Models](https://opencv.org/blog/deep-learning-model-training/) - OpenCV blog
* [What is model training?](https://www.ibm.com/think/topics/model-training) - IBM Think article

# Concepts

- Maching Learning Model
  - Artificial neural networks
  - Decision trees
  - Random forest regression
  - Support-vector machines
  - Regression analysis
  - Bayesian networks
  - Gaussian processes
  - Genetic algorithms
  - Belief functions
  - Rule-based models

A machine learning model is a type of mathematical model that, once "trained" on a given dataset, can be used to make predictions or classifications on new data. During training, a learning algorithm iteratively adjusts the model's internal parameters to minimise errors in its predictions. By extension, the term "model" can refer to several levels of specificity, from a general class of models and their associated learning algorithms to a fully trained model with all its internal parameters tuned. - [wikipedia](https://en.wikipedia.org/wiki/Machine_learning)

- Model training
Model training is the process of “teaching” a machine learning model to optimize performance on a training dataset of sample tasks relevant to the model’s eventual use cases. If training data closely resembles real-world problems that the model will be tasked with, learning its patterns and correlations will enable a trained model to make accurate predictions on new data. - 'What is model training?' IBM Think article

# General workflow

steps: - 'What is model training?' IBM Think article
- Model selection
- Data collection
- Data preparation
- Selecting hyperparameters
  - learning rate: learning schedule
  - number of hidden layers
  - number of neurons per hidden layer
  - optimizer
  - batch size
  - activation function
  - number of iterations: use early stopping instead
  - ...
- Performance on training data
- Calculating loss (or reward)
- Optimizing parameters 
- Model evaluation

# Facing problems
* [Vanishing gradient problem](https://en.wikipedia.org/wiki/Vanishing_gradient_problem): 梯度消失问题
  - Xavier/Glorot initialization
  - LeCun initialization
  - He/Kaiming initialization
  - better activation functions
    - sigmoid, ReLU
    - LeakyReLU, RReLU(randomized leaky ReLU), PReLU(parametric leaky ReLU)
    - ELU(exponential linear unit), SELU(scaled ELU)
    - GELU, SiLU(sigmoid linear unit)
    - Swish
    - Mish
  - BN(batch normalization)
  - gradient clipping

# Hyperparameter tuning
* https://en.wikipedia.org/wiki/Hyperparameter_optimization
* [Population Based Training of Neural Networks](https://arxiv.org/abs/1711.09846) - 2017, evolutionary algorithm
* [Welcoming the Era of Deep Neuroevolution](https://www.uber.com/en-SG/blog/deep-neuroevolution/) - 2017, Uber

approaches
- Grid search
- Random search
- Bayesian optimization
- Gradient-based optimization
- Evolutionary optimization
- Population-based
- Early stopping-based
- RBF, spectral, ...

# Fast Optimizer
* regular: gradient descent optimizer
* momentum/动量
* Nesterov accelerated gradient
* AdaGrad
* RMSProp
* Adam(adaptive moment estimation) and its variants

more:
- [TensorFlow Model Optimization Toolkit](https://www.tensorflow.org/model_optimization/)

# Learning rate schedule
* https://en.wikipedia.org/wiki/Learning_rate#Learning_rate_schedule
* [An empirical study of learning rates in deep neural networks for speech recognition](https://research.google.com/pubs/archive/40808.pdf)

A learning rate schedule changes the learning rate during learning and is most often changed between epochs/iterations. This is mainly done with two parameters: **decay** and **momentum**.

- Power scheduling
- Exponential scheduling
- Piecewise constant scheduling
- Performance scheduling
- 1cycle scheduling


# Regularization


* $\ell_{1}$ regularization
* $\ell_{2}$ regularization
* dropout
  - [Dropout: A Simple Way to Prevent Neural Networks from Overfitting](https://jmlr.org/papers/v15/srivastava14a.html) - 2014
* max-norm regularization