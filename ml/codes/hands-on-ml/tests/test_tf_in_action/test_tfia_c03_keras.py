"""TensorFlow in Action
Keras main APIs:
- Sequential: start with one input, a sequence of layers, end with one input
- Functional: multiple inputs, parallel layers, multiple outputs
- Sub-classing: a Python object represents model or layer, use the low-level functionality of TF
"""


from typing import override
import unittest
import os
import requests
import pandas as pd
import tensorflow as tf

# pylint: skip-file


class TestKeras(unittest.TestCase):
  def setUp(self):
    self.data_path = 'data/tf_in_action/iris.data'
    if not os.path.exists(self.data_path):
      print(f'not found {self.data_path}, download...')
      url = "https://archive.ics.uci.edu/ml/machine-learning-databases/iris/iris.data"
      r = requests.get(url)
      with open(self.data_path, 'wb') as f:
        f.write(r.content)

    self.iris_df = pd.read_csv(self.data_path, header=None)
    self.assertIsNotNone(self.iris_df)
    self.iris_df.columns = ['sepal_length', 'sepal_width',
                            'petal_width', 'petal_length', 'label']
    self.iris_df["label"] = self.iris_df["label"].map(
        {'Iris-setosa': 0, 'Iris-versicolor': 1, 'Iris-virginica': 2})

    self.iris_df = self.iris_df.sample(frac=1.0, random_state=4321)
    self.x = self.iris_df[["sepal_length", "sepal_width",
                           "petal_width", "petal_length"]]
    self.x = self.x - self.x.mean(axis=0)
    print(self.iris_df.info())
    # one-hot encoding
    self.y = tf.one_hot(self.iris_df["label"], depth=3)

  def test_sequential_api(self) -> None:
    # from tensorflow.keras.layers import Dense
    # from tensorflow.keras.models import Sequential
    # import tensorflow.keras.backend as K
    # or
    # from tensorflow.python.keras.layers import Dense
    # or
    from keras.layers import Dense
    from keras.models import Sequential
    import keras.backend as K
    K.clear_session()
    model = Sequential()
    model.add(Dense(32, activation='relu', input_shape=(4,)))
    model.add(Dense(16, activation='relu'))
    model.add(Dense(3, activation='softmax'))

    model.compile(loss='categorical_crossentropy',
                  optimizer='adam', metrics=['acc'])

    model.summary()

    history = model.fit(self.x, self.y, batch_size=64, epochs=25)
    from src.util.tf import plot_history
    plot_history(history)

  def test_functional_api(self) -> None:
    from keras.layers import Input, Dense, Concatenate
    from keras.models import Model
    import keras.backend as K

    K.clear_session()

    input1 = Input(shape=(4,))
    input2 = Input(shape=(2,))  # PCA feature
    out1 = Dense(16, activation='relu')(input1)
    out2 = Dense(16, activation='relu')(input2)
    out = Concatenate(axis=1)([out1, out2])
    out = Dense(16, activation='relu')(out)
    out = Dense(3, activation='softmax')(out)

    model = Model(inputs=[input1, input2], outputs=out)

    model.compile(loss='categorical_crossentropy',
                  optimizer='adam', metrics=['acc'])
    model.summary()
    # model_path = 'data/tf_in_action/models/model.png'
    # keras.utils.plot_model(model, show_shapes=True, to_file=model_path)
    # from PIL import Image
    # Image.open(model_path).show()

    from sklearn.decomposition import PCA
    pca_model = PCA(n_components=2, random_state=42)
    x_pca = pca_model.fit_transform(self.x)

    history = model.fit([self.x, x_pca], self.y, batch_size=64, epochs=10)
    from src.util.tf import plot_history
    plot_history(history)

  def test_subclassing_api(self) -> None:
    from keras import layers

    class MulBiasDense(layers.Layer):
      def __init__(self, units=32, input_dim=32, activation=None):
        super(MulBiasDense, self).__init__()
        self.units = units
        self.activation = activation

      @override
      def build(self, input_shape):
        self.w = self.add_weight(shape=(input_shape[-1], self.units),
                                 initializer='glorot_uniform', trainable=True)
        self.b = self.add_weight(
            shape=(self.units,), initializer='glorot_uniform', trainable=True)
        self.b_mul = self.add_weight(
            shape=(self.units,), initializer='glorot_uniform', trainable=True)

      @override
      def call(self, inputs) -> None:
        out = (tf.matmul(inputs, self.w) + self.b) * self.b_mul
        return layers.Activation(self.activation)(out)

    from keras.layers import Input, Dense
    from keras.models import Model
    import keras.backend as K

    K.clear_session()
    input = Input(shape=(4,))
    out = MulBiasDense(units=32, activation='relu')(input)
    out = MulBiasDense(units=16, activation='relu')(out)
    out = Dense(3, activation='softmax')(out)

    model = Model(inputs=input, outputs=out)
    model.compile(loss='categorical_crossentropy',
                  optimizer='adam', metrics=['acc'])

    history = model.fit(self.x, self.y, batch_size=64, epochs=10)
    from src.util.tf import plot_history
    plot_history(history)
