# Terminology

# Activation function/激活函数
* https://en.wikipedia.org/wiki/Activation_function

In artificial neural networks, the activation function of a node is **a function that calculates the output of the node based on its individual inputs and their weights**. Nontrivial problems can be solved using only a few nodes if the activation function is nonlinear.

# Attention/注意力机制
* https://en.wikipedia.org/wiki/Attention_(machine_learning)

In machine learning, attention is **a method that determines the importance of each component in a sequence relative to the other components in that sequence**. In natural language processing, importance is represented by "soft" weights assigned to each word in a sentence. More generally, attention encodes vectors called token embeddings across a fixed-width sequence that can range from tens to millions of tokens in size.

# Autoencoder/自动编码器
* https://en.wikipedia.org/wiki/Autoencoder
* https://arxiv.org/abs/2003.05991

An autoencoder is a type of artificial neural network used to learn efficient codings of unlabeled data (unsupervised learning). An autoencoder learns two functions: an encoding function that transforms the input data, and a decoding function that recreates the input data from the encoded representation. The autoencoder learns an efficient representation (encoding) for a set of data, typically for dimensionality reduction, to generate lower-dimensional embeddings for subsequent use by other machine learning algorithms.

# Bias–variance tradeoff/偏差-方差权衡
* https://en.wikipedia.org/wiki/Bias%E2%80%93variance_tradeoff

In statistics and machine learning, the bias–variance tradeoff describes the relationship between a model's complexity, the accuracy of its predictions, and how well it can make predictions on previously unseen data that were not used to train the model.

# CNN: Convolutional Neural Network

# Decision tree learning/决策树学习
* https://en.wikipedia.org/wiki/Decision_tree_learning

Decision tree learning is a supervised learning approach used in statistics, data mining and machine learning. In this formalism, a *classification* or *regression* decision tree is used as a predictive model to draw conclusions about a set of observations.

# Deep Learning/深度学习
* https://en.wikipedia.org/wiki/Deep_learning

In machine learning, deep learning focuses on utilizing multilayered neural networks to perform tasks such as classification, regression, and representation learning.

Some common deep learning network architectures include 
- fully connected networks, 
- deep belief networks, 
- RNN(recurrent neural networks): 循环神经网络, 
- CNN(convolutional neural networks): 卷积神经网络, 
- GAN(generative adversarial networks): 生成对抗网络, 
- transformers, and 
- neural radiance fields.

# Ensemble Learning/集成学习
* https://en.wikipedia.org/wiki/Ensemble_learning

在统计学和机器学习中, 集成学习(Ensemble learning)方法通过组合多种学习算法来获得比单独使用任何一种算法更好的预测性能.

# Evolution strategy/进化策略
* https://en.wikipedia.org/wiki/Evolution_strategy
* [Evolution Strategies as a Scalable Alternative to Reinforcement Learning](https://arxiv.org/abs/1703.03864)
* [A Visual Guide to Evolution Strategies](https://blog.otoro.net/2017/10/29/visual-evolution-strategies/)

Evolution strategy (ES) from computer science is a subclass of evolutionary algorithms(进化算法), which serves as an optimization technique. It uses the major genetic operators(遗传算子) mutation(突变), recombination(重组) and selection of parents(亲本选择).

# Evolutionary algorithm/进化算法
* https://en.wikipedia.org/wiki/Evolutionary_algorithm

Evolutionary algorithms (EA) reproduce essential elements of biological evolution in a computer algorithm in order to solve "difficult" problems, at least approximately, for which no exact or satisfactory solution methods are known. They are metaheuristics and population-based bio-inspired algorithms(元启发和基于种群的生物启发式) and evolutionary computation(进化计算), which itself are part of the field of computational intelligence. The mechanisms of biological evolution that an EA mainly imitates are reproduction(繁殖), mutation(突变), recombination(重组) and selection(选择). Candidate solutions to the optimization problem play the role of individuals in a population, and the fitness function determines the quality of the solutions (see also loss function). Evolution of the population then takes place after the repeated application of the above operators.

types:
- Genetic algorithm/遗传算法
- Genetic programming/遗传编程
- Evolutionary programming/进化规划
- Evolution strategy (ES)/进化策略
- Differential evolution/差分进化
- Coevolutionary algorithm/协同进化
- Neuroevolution/神经进化
- Learning classifier system/学习分类器系统
- Quality–Diversity algorithms/质量与多样性算法

# Exploratory Data Analysis/探索性数据分析
* https://en.wikipedia.org/wiki/Exploratory_data_analysis

See Also 
- [DataExploratory.ipynb](./theory/Data%20Exploratory.ipynb)
- Practical Statistics for Data Scientists

# Fine-tuning/微调
* https://en.wikipedia.org/wiki/Fine-tuning_(deep_learning)

In deep learning, fine-tuning is an approach to *transfer learning* in which the parameters of a pre-trained neural network model are trained on new data. 
Fine-tuning can be done on the entire neural network, or on only a subset of its layers, in which case the layers that are not being fine-tuned are "frozen" (i.e., not changed during backpropagation). 
A model may also be augmented with "adapters"—lightweight modules inserted into the model's architecture that nudge the embedding space for domain adaptation. These contain far fewer parameters than the original model and can be fine-tuned in a parameter-efficient way by tuning only their weights and leaving the rest of the model's weights frozen.

# Hyperparameter/超参数
* https://en.wikipedia.org/wiki/Hyperparameter_(machine_learning)

In machine learning, a hyperparameter is **a parameter that can be set in order to define any configurable part of a model's learning process**. Hyperparameters can be classified as either **model hyperparameters** (such as the topology and size of a neural network) or **algorithm hyperparameters** (such as the learning rate and the batch size of an optimizer). These are named hyperparameters in contrast to *parameters*, which are characteristics that the model learns from the data.

# Learning curve/学习曲线
* https://en.wikipedia.org/wiki/Learning_curve_(machine_learning)

In machine learning (ML), a learning curve (or training curve) is a graphical representation that shows how a model's performance on a training set (and usually a validation set) changes with the number of training iterations (epochs) or the amount of training data. Typically, the number of training epochs or training set size is plotted on the x-axis, and the value of the loss function (and possibly some other metric such as the cross-validation score) on the y-axis.

# NA

NA, stands fro **not available**. In statistics application NA data may either be data that does not exist or that exists but wat not observed.

In pandas, there are NA handling object methods:
- `dropna`
- `fillna`
- `isna`
- `notna`

# Naive Bayes classifier/朴素贝叶斯分类器
* https://en.wikipedia.org/wiki/Naive_Bayes_classifier

In statistics, naive (sometimes simple or idiot's) Bayes classifiers are a family of "probabilistic classifiers" which *assumes that the features are conditionally independent*, given the target class.

# PCA: Principle Component Analysis/主成分分析

# Regularization/正则化
* https://en.wikipedia.org/wiki/Regularization_(mathematics)

In mathematics, statistics, finance, and computer science, particularly in machine learning and inverse problems, regularization is a process that converts the answer to a problem to a simpler one. It is often used in solving ill-posed problems(不适定问题) or to prevent overfitting(避免过拟合).

# ROC curve: Receiver Operating Characteristic
* https://en.wikipedia.org/wiki/Receiver_operating_characteristic
* [Understanding ROC curves](http://www.navan.name/roc/)

A receiver operating characteristic curve, or ROC curve, is a graphical plot that illustrates the performance of a binary classifier model (although it can be generalized to multiple classes) at varying threshold values.

The ROC curve is the plot of the true positive rate (TPR) against the false positive rate (FPR) at each threshold setting.

# SGD: Stochastic gradient descent/随机梯度下降
* https://en.wikipedia.org/wiki/Stochastic_gradient_descent

Stochastic gradient descent (often abbreviated SGD) is **an iterative method for optimizing an objective function with suitable smoothness properties** (e.g. differentiable or subdifferentiable). It can be regarded as a stochastic approximation of gradient descent optimization, since it replaces the actual gradient (calculated from the entire data set) by an estimate thereof (calculated from a randomly selected subset of the data). Especially in high-dimensional optimization problems this reduces the very high computational burden, achieving faster iterations in exchange for a lower convergence rate.

# t-SNE: t-Distributed Stochastic Neighbor Embedding

# Transfer learning/迁移学习
* https://en.wikipedia.org/wiki/Transfer_learning

Transfer learning (TL) is a technique in machine learning (ML) in which knowledge learned from a task is re-used in order to boost performance on a related task.

# Transformers
* https://en.wikipedia.org/wiki/Transformer_(deep_learning_architecture)

In deep learning, transformer is a neural network architecture based on the **multi-head attention mechanism**, in which text is converted to numerical representations called *tokens*, and each token is converted into a vector via lookup from a word embedding table. At each layer, each token is then contextualized within the scope of the context window with other (unmasked) tokens via a parallel multi-head attention mechanism, allowing the signal for key tokens to be amplified and less important tokens to be diminished.

# Vanishing gradient problem/梯度消失问题
* https://en.wikipedia.org/wiki/Vanishing_gradient_problem

梯度消失问题: 基于梯度的学习方法中, 权重的更新是与当前权重上的错误函数的偏导成比例的. 在一些情况下, 梯度极其的小, 权重无法有效更新.