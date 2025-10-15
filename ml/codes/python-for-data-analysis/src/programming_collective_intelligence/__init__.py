"""
Programming Collective Intelligence
- 协同过滤(collaborative filtering)
- 聚类(clustering)
- 搜索与排名(ranking)
- PageRank
- 神经网络(neural network)
- 优化算法(optimization)
- 爬山法(hill climbing)
- 模拟退火(simulated annealing)
- 遗传算法(genetic algorithms)
- 贝叶斯分类器(Bayes Classifier)
- 决策树(decision tree)
- k-最近邻(k-nearest neighbors)
- 核方法(kernel method, kernel tricks)
- 支持向量机(support vector machine)
- 特征提取(feature extraction)
- 非负矩阵隐式分解(non-negative matrix factorization)
- 遗传编程(genetic programming)
"""

# TODO: add type hint

WORKING_DIR = "data/pci/"

CRAWLER_WORKING_DIR = WORKING_DIR + "crawler/"

# NLTK's list of english stopwords: https://gist.github.com/sebleier/554280
STOP_WORDS = ['i', 'me', 'my', 'myself', 'we', 'our', 'ours', 'ourselves',
              'you', "you're", "you've", "you'll", "you'd", 'your', 'yours',
              'yourself', 'yourselves', 'he', 'him', 'his', 'himself', 'she',
              "she's", 'her', 'hers', 'herself', 'it', "it's", 'its', 'itself',
              'they', 'them', 'their', 'theirs', 'themselves', 'what', 'which',
              'who', 'whom', 'this', 'that', "that'll", 'these', 'those', 'am',
              'is', 'are', 'was', 'were', 'be', 'been', 'being', 'have', 'has',
              'had', 'having', 'do', 'does', 'did', 'doing', 'a', 'an', 'the',
              'and', 'but', 'if', 'or', 'because', 'as', 'until', 'while', 'of',
              'at', 'by', 'for', 'with', 'about', 'against', 'between', 'into',
              'through', 'during', 'before', 'after', 'above', 'below', 'to',
              'from', 'up', 'down', 'in', 'out', 'on', 'off', 'over', 'under',
              'again', 'further', 'then', 'once', 'here', 'there', 'when',
              'where', 'why', 'how', 'all', 'any', 'both', 'each', 'few',
              'more', 'most', 'other', 'some', 'such', 'no', 'nor', 'not',
              'only', 'own', 'same', 'so', 'than', 'too', 'very', 's', 't',
              'can', 'will', 'just', 'don', "don't", 'should', "should've",
              'now', 'd', 'll', 'm', 'o', 're', 've', 'y', 'ain', 'aren',
              "aren't", 'couldn', "couldn't", 'didn', "didn't", 'doesn',
              "doesn't", 'hadn', "hadn't", 'hasn', "hasn't", 'haven',
              "haven't", 'isn', "isn't", 'ma', 'mightn', "mightn't",
              'mustn', "mustn't", 'needn', "needn't", 'shan', "shan't",
              'shouldn', "shouldn't", 'wasn', "wasn't", 'weren', "weren't",
                    'won', "won't", 'wouldn', "wouldn't"]
