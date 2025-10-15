"""TensorFlow in Action
Transformers
"""


from typing import override
import unittest
import tensorflow as tf
from keras.layers import Layer, Dense, Input, Embedding
from keras.models import Model
import math
# pylint: skip-file


class SelfAttentionLayer(Layer):
  """ Defines the computations in the self attention layer """

  def __init__(self, d):
    super(SelfAttentionLayer, self).__init__()
    # Feature dimensionality of the output
    self.d = d

  def build(self, input_shape):
    # Query weight matrix
    self.Wq = self.add_weight(
        shape=(input_shape[-1], self.d), initializer='glorot_uniform',
        trainable=True, dtype='float32'
    )
    # Key weight matrix
    self.Wk = self.add_weight(
        shape=(input_shape[-1], self.d), initializer='glorot_uniform',
        trainable=True, dtype='float32'
    )
    # Value weight matrix
    self.Wv = self.add_weight(
        shape=(input_shape[-1], self.d), initializer='glorot_uniform',
        trainable=True, dtype='float32'
    )

  def call(self, q_x, k_x, v_x, mask=None):
    # Computing query, key and value
    q = tf.matmul(q_x, self.Wq)  # [None, t, d]
    k = tf.matmul(k_x, self.Wk)  # [None, t, d]
    v = tf.matmul(v_x, self.Wv)  # [None, t, d]

    # Computing the probability matrix
    p = tf.matmul(q, k, transpose_b=True)/math.sqrt(self.d)  # [None, t, t]

    if mask is None:
      p = tf.nn.softmax(p)
    else:
      # Creating the mask
      p += mask * -1e9
      p = tf.nn.softmax(p)

    # Computing the final output
    h = tf.matmul(p, v)  # [None, t, t] . [None, t, d] => [None, t, d]
    return h, p


class FCLayer(Layer):
  """ The computations of a fully connected sublayer """

  def __init__(self, output_dim1: int, output_dim2: int):
    super(FCLayer, self).__init__()
    # Dimensionality of the first hidden layer
    # self.output_dim1 = output_dim1
    # Dimensionality of the second hidden layer
    # self.output_dim2 = output_dim2
    self.dense_layer_1 = Dense(output_dim1, activation='relu')
    self.dense_layer_2 = Dense(output_dim2)

  # @override
  # def build(self, input_shape):
  #   # First layer's weights and biases
  #   self.W1 = self.add_weight(shape=(input_shape[-1], self.output_dim1), initializer='glorot_uniform',
  #                             trainable=True, dtype='float32')
  #   self.b1 = self.add_weight(shape=(self.output_dim1,), initializer='glorot_uniform',
  #                             trainable=True, dtype='float32')
  #   self.W2 = self.add_weight(shape=(input_shape[-1], self.output_dim2), initializer='glorot_uniform',
  #                             trainable=True, dtype='float32')
  #   self.b2 = self.add_weight(shape=(self.output_dim2,), initializer='glorot_uniform',
  #                             trainable=True, dtype='float32')

  @override
  def call(self, x):
    # # Computing the first fully connected output
    # ff1 = tf.nn.relu(tf.matmul(x, self.W1) + self.b1)
    # # Computing the second fully connected output
    # # Note that the second layer doesn't use an activation
    # ff2 = tf.matmul(ff1, self.W2) + self.b2
    # return ff2
    ff1 = self.dense_layer_1(x)
    ff2 = self.dense_layer_2(ff1)
    return ff2


class EncoderLayer(Layer):
  """ The Encoder layer """

  def __init__(self, d, n_heads):
    super(EncoderLayer, self).__init__()
    # Feature dimensionality
    self.d = d
    # Dimensionality of a head
    self.d_head = int(d/n_heads)
    # Number of heads
    self.n_heads = n_heads
    # Actual attention heads
    self.attn_heads = [SelfAttentionLayer(
        self.d_head) for i in range(self.n_heads)]
    # Fully connected layer
    self.fc_layer = FCLayer(2048, self.d)

  def call(self, x):

    def compute_multihead_output(x):
      """ Computing the multi head attention output"""
      outputs = [head(x, x, x)[0] for head in self.attn_heads]
      outputs = tf.concat(outputs, axis=-1)
      return outputs

    # Multi head attention layer output
    h1 = compute_multihead_output(x)
    # Fully connected layer output
    y = self.fc_layer(h1)

    return y


class DecoderLayer(Layer):
  def __init__(self, dim: int, n_heads: int):
    super(DecoderLayer, self).__init__()
    self.dim = dim
    self.d_heads = int(dim/n_heads)
    self.dec_attn_heads = [SelfAttentionLayer(
        self.d_heads) for i in range(n_heads)]
    self.attn_heads = [SelfAttentionLayer(
        self.d_heads) for i in range(n_heads)]
    self.fc_layer = FCLayer(2048, self.dim)

  @override
  def call(self, de_x, en_x, mask=None):
    def compute_multihead_output(attn_heads, de_x, en_x, mask=None):
      outputs = [head(en_x, en_x, de_x, mask)[0] for head in self.attn_heads]
      outputs = tf.concat(outputs, axis=-1)
      return outputs

    h1 = compute_multihead_output(self.dec_attn_heads, de_x, de_x, mask)
    h2 = compute_multihead_output(self.attn_heads, h1, en_x)
    y = self.fc_layer(h2)
    return y


class TestTransformers(unittest.TestCase):
  def test_model(self):
    # Defining some hyperparameters
    n_steps = 25  # Sequence length
    n_en_vocab = 300  # Encoder's vocabulary size
    n_de_vocab = 400  # Decoder's vocabulary size
    n_heads = 8  # Number of attention heads
    d = 512  # The feature dimensionality of each layer

    # Look-ahead mask
    mask = 1 - tf.linalg.band_part(tf.ones((n_steps, n_steps)), -1, 0)

    # Encoder input layer
    en_inp = Input(shape=(n_steps,))
    # Encoder input embedddings
    en_emb = Embedding(n_en_vocab, 512, input_length=n_steps)(en_inp)

    # Two encoder layers
    en_out1 = EncoderLayer(d, n_heads)(en_emb)
    en_out2 = EncoderLayer(d, n_heads)(en_out1)

    # Decoder input layer
    de_inp = Input(shape=(n_steps,))
    # Decoder input embeddings
    de_emb = Embedding(n_de_vocab, 512, input_length=n_steps)(de_inp)

    # Two decoder layers
    de_out1 = DecoderLayer(d, n_heads)(de_emb, en_out2, mask)
    de_out2 = DecoderLayer(d, n_heads)(de_out1, en_out2, mask)

    # Final output layer
    de_pred = Dense(n_de_vocab, activation='softmax')(de_out2)

    # Defining the model
    transformer = Model(
        inputs=[en_inp, de_inp], outputs=de_pred, name='MinTransformer')
    # Compiling the model
    transformer.compile(loss='categorical_crossentropy',
                        optimizer='adam', metrics=['acc'])
    transformer.summary()
