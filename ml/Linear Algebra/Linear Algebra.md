# Linear Algebra

books:
* Leon, S. J. **Linear Algebra with Applications**. Pearson, 2014.
* Cohen, M. X. **Practical Linear Algebra for Data Science**. O'Reilly Media, 2022.

# Terminology

* 矩阵与方程组(Matrices and System of Equations)
  * 线性方程组(System of Linear Equations)
    * 初等行运算(Elementary Row Operations)
  * 行阶梯型(Row Echelon Form)
  * 标量(Scalar), 向量(Vector), 矩阵(Matrices)
  * 矩阵代数(Matrix Algebra)
    * 向量乘积(vector multiplication): 点积(dot product), 叉积(cross product)
  * 矩阵转置(Matrix Transpose)
  * 初等矩阵(Elementary Matrices)
  * 分块矩阵(Partitioned Matrices)

* 行列式(Determinants)

* 向量空间(Vector Spaces)
  * 子空间(Subspaces)
  * 线性独立(Linear Independence)
  * 基(Basis), 维度(Dimension)
  * 基变换(Change of Basis)
  * 行空间(Row Space), 列空间(Column Space)

* 线性转换(Linear Transformations)
* 线性变换的矩阵表示(Matrix Representation of Linear Transformations)
  * 相似性(Similarity)

* 正交性(Orthogonality)
  * 正交子空间(Orthogonal Subspaces)
  * 最小二乘问题(Least Squares Problems)
  * 内积空间(Inner Product Spaces)
  * 正交集(Orthonormal Sets)
  * 格拉姆-施密特正交化过程(Gram-Schmidt Orthogonalization Process)
  * 正交多项式(Orthogonal Polynomials)

* 特征值(Engenvalues)
  * 特征值(Eigenvalue), 特征向量(Eigenvector)
  * 特征值分解(Eigenvalue Decomposition)
  * 对角化(Diagonalization)
  * 埃尔米特矩阵(Hermitian Matrices)
  * 奇异值分解(Singular Value Decomposition(SVD))
  * 二次型(Quadratic Forms)
  * 正定矩阵(Positive Definite Matrices)

* 数值线性代数(Numerical Linear Algebra)
  * 浮点数(Floating-Point Numbers)
  * 高斯消元法(Gaussian Elimination)
  * 矩阵范数(Matrix Norm)
    * 欧几里德范数(Euclidean Norm)
  * 条件数(Condition Numbers)

# 矩阵与方程组

初等行运算:

* I. 交换两行.
* II. 以非零实数乘以某行.
* III. 将某行替换为它与其它行的倍数的和.

矩阵算术:

行向量(row vector) $\overrightarrow	
{\bold{x}} = (x_{1}, x_{2}, \dots, x_{n})$

列向量(column vector)
$$
\bold{x} = \begin{bmatrix}
   x_{1} \\
	 x_{2} \\
   \vdots \\
	 x_{n} 
\end{bmatrix}
$$


矩阵代数: 标量$\alpha, \beta$, 矩阵$A, B, C$

* 一般的, 矩阵乘法不满足交换律: $$AB \ne BA$$. 
* $A + B = B + A$
* $(A + B) + C = A + (B + C)$
* $(AB)C = A(BC)$ : 简写为 $ABC$
* $A(B + C) = AB + AC$
* $(A + B)C = AC + BC$
* $(\alpha \beta)A = \alpha(\beta A)$
* $\alpha (AB) = (\alpha A)B = A(\alpha B)$
* $(\alpha + \beta)A = \alpha A + \beta A$
* $\alpha (A + B) = \alpha A + \alpha B$

# 行列式

# 向量空间

# 线性变换

# 正交性

# 特征值

# 数值线性代数

# Symbols

column vector and row vector:
$$
\bold{x} = \begin{bmatrix}
   1 \\
	 4 \\
   5 \\
	 6 
\end{bmatrix}
\\
\bold{y} = \begin{bmatrix}
   .3 \\
	 -7
\end{bmatrix}
\\
\bold{z} = \begin{bmatrix}
   1 & 4 & 5 & 6
\end{bmatrix}
$$

vector norm:
$$
\lVert \bold{v} \rVert = \sqrt{\sum_{i=1}^{n} v_{i}^{2}}
$$

unit vector: 
$$
\hat{\bold{v}} = \frac{1}{\| \bold{v} \|} \bold{v}
$$

vector dot product:

$$
\delta = \sum_{i=1}^{n}a_{i} b_{i} \\
\lang \bold{a}, \bold{b}\rang
$$

vector set: 
$$
V = \{ \bold{v_{1}}, \cdots, \bold{v_{n}} \}
$$

linear weighted combination: 
$$
\bold{w} = \lambda_{1}\bold{v_{1}} \lambda_{2}\bold{v_{2}} + \cdots + \lambda_{n}\bold{v_{n}}
$$

linear dependence: 
$$
\bold{0} = \lambda_{1} \bold{v_{1}} + \lambda_{2} \bold{v_{2}} + \cdots + \lambda_{n} \bold{v_{n}}, \lambda_{i} \in \reals
$$

Matrix: $\bold{A}$, size $M \times N$ (row by column)

$$
\begin{bmatrix}
   1 & 2 \\
   \pi & 4 \\
   6 & 7
\end{bmatrix}
\\
\begin{bmatrix}
   -6 & 1/3 \\
   e^{4.3} & -1.4 \\
   6/5 & 0
\end{bmatrix}
$$

Identity Matrix: $\bold{I}$

Zero Matrix: $\bold{0}$

Matrix addition:
$$
\begin{bmatrix}
2 & 3 & 4 \\
1 & 2 & 4
\end{bmatrix} +
\begin{bmatrix}
0 & 3 & 1 \\
-1 & -4 & 2
\end{bmatrix} = 
\begin{bmatrix}
(2+0) & (3+3) & (4+1) \\
(1-1) & (2-4) & (4+2)
\end{bmatrix}
= 
\begin{bmatrix}
2 & 6 & 5 \\
0 & -2 & 6
\end{bmatrix}
$$

shift a matrix: $\bold{A} = \boldsymbol{\lambda} \bold{I}$

scalar-matrix multiplication:
$$
\gamma \begin{bmatrix}
a & b \\
c & d
\end{bmatrix} =
\begin{bmatrix}
\gamma a & \gamma b \\
\gamma c & \gamma d
\end{bmatrix}
$$

Hadamard multiplication(element-wise multiplication):
$$
\begin{bmatrix}
2 & 3\\
4 & 5
\end{bmatrix} \odot
\begin{bmatrix}
a & b \\
c & d
\end{bmatrix} =
\begin{bmatrix}
2a & 3b \\
4c & 5d
\end{bmatrix}
$$

Matrix multiplication:
$$
\begin{bmatrix}
2 & 3\\
4 & 5
\end{bmatrix} 
\begin{bmatrix}
a & b \\
c & d
\end{bmatrix} =
\begin{bmatrix}
(2a+3c) & (2b+3d) \\
(4a+5c) & (4b+5d)
\end{bmatrix}
$$

Matrix-vector multiplication: $\bold{A} \bold{v}$, $\bold{v}^{T} \bold{A}$

Matrix transpose:
$$
a_{i,j}^{T} = a_{j,i} \\
$$

$$
\begin{bmatrix}
3 & 0 & 4 \\
9 & 8 & 3
\end{bmatrix}^{T} =
\begin{bmatrix}
3 & 9 \\
0 & 8 \\
4 & 3
\end{bmatrix}
$$

Matrix Frobenius norm:
$$
\lVert \bold{A} \rVert_{F} = \sqrt{\sum_{i=1}^{M}\sum_{j=1}^{N}a_{ij}^{2}}
$$

p-norm:
$$
\lVert \bold{A} \rVert_{p} = \left ( \sum_{i=1}^{M}\sum_{j=1}^{N}|a_{ij}|^{p} \right )^{1/p}
$$

Matrix column space: $C(\bold{A})$

Matrix row space: $R(\bold{A})$

Matrix null space: $N(\bold{A})$

Matrix rank: $r(\bold{A})$, $\texttt{rank}(\bold{A})$

augmented matrix: $\bold{\widetilde{A}}$

Matrix determinate: $\texttt{det}(\bold{A})$, $|\bold{A}|$

orthogonal matrix: $\bold{Q}$
$$
\bold{Q}^{T} \bold{Q} = \bold{I}
$$

QR decomposition: $\bold{A} = \bold{Q} \bold{R}$

QR and inverse:
$$
\begin{align}
   \bold{A} &= \bold{Q} \bold{R} \\
   \bold{A}^{-1} &= (\bold{Q} \bold{R})^{-1} \\
   \bold{A}^{-1} &= \bold{R}^{-1} \bold{Q}^{-1} \\
   \bold{A}^{-1} &= \bold{R}^{-1} \bold{Q}^{T}
\end{align}
$$

Matrix equation:
$$
\begin{align}
   x + y &= 4 \\
   -x/2 + y &= 2
\end{align}
$$
$$
\begin{bmatrix}
   1 & 1 \\
   -1/2 & 1
\end{bmatrix}
\begin{bmatrix}
   x \\
   y
\end{bmatrix}
= 
\begin{bmatrix}
   4 \\
   2
\end{bmatrix}
$$

LU decomposition: $\bold{A} = \bold{L} \bold{U}$

permutation matrix: $\bold{P}$

general linear model: $\bold{X} \boldsymbol{\beta} = \bold{y}$

Least Squares Solution to general linear model:
$$
\begin{align}
\bold{X} \boldsymbol{\beta} &= \bold{y} \\
(\bold{X}^{T} \bold{X})^{-1} \bold{X}^{T} \bold{X} \boldsymbol{\beta} &= (\bold{X}^{T} \bold{X})^{-1} \bold{X}^{T} \bold{y} \\
\boldsymbol{\beta} &= (\bold{X}^{T} \bold{X})^{-1} \bold{X}^{T} \bold{y}
\end{align}
$$

Least Squares via QR:
$$
\begin{align}
\bold{X} \boldsymbol{\beta} &= \bold{y} \\
\bold{Q} \bold{R} \boldsymbol{\beta} &= \bold{y} \\
\bold{R} \boldsymbol{\beta} &= \bold{Q}^{T} \bold{y} \\
\boldsymbol{\beta} &= \bold{R}^{-1} \bold{Q}^{T} \bold{y}
\end{align}
$$

Enginevalue:
$$
\bold{A} \bold{v} = \lambda \bold{v}
$$

Singular Value Decomposistion(SVD)
$$
\bold{A}_{M \times N} = \bold{U}_{M \times M} \bold{\Sigma}_{M \times N} \bold{V}_{N \times N}^{T}, M \ge N
\\
\\
\bold{\Sigma} = \begin{bmatrix}
   \sigma_{1} &  & &\\
    & \sigma_{2} & &\\
    &  & \ddots &\\
    & & & \sigma_{N} \\
    & & & \\
    & & &
\end{bmatrix}
\\
\sigma_{1} \ge \sigma_{2} \ge \cdots \ge \sigma_{n} \ge 0

$$

here $\bold{U}$ and $\bold{V}$ are orthogonal matrices, $\sigma_{i}$ are the singular value of $\bold{A}$.


