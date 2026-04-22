# Knowledge Graph
* https://en.wikipedia.org/wiki/Knowledge_graph


In knowledge representation and reasoning, a knowledge graph is a knowledge base that uses a graph-structured data model or topology to represent and operate on data.
Knowledge graphs are often used to store interlinked descriptions of entities – objects, events, situations or abstract concepts – while also encoding the free-form semantics or relationships underlying these entities.

Since the development of the Semantic Web/语义网络, knowledge graphs have often been associated with linked open data projects, focusing on the connections between concepts and entities.
They are also historically associated with and used by search engines/搜索引擎 such as Google, Bing, and Yahoo; knowledge engines/知识引擎 and question-answering services/问答服务 such as WolframAlpha, Apple's Siri, and Amazon Alexa; and social networks/社交网络 such as LinkedIn and Facebook.

Recent developments in data science and machine learning, particularly in graph neural networks/图神经网络 and representation learning/表示学习 and also in machine learning, have broadened the scope of knowledge graphs beyond their traditional use in search engines/搜索引擎 and recommender systems/推荐系统.
They are increasingly used in scientific research, with notable applications in fields such as genomics, proteomics, and systems biology.

# See Also
* [knowledge_graph](https://github.com/rahulnyk/knowledge_graph): Convert any text to a graph of knowledge. This can be used for Graph Augmented Generation or Knowledge Graph based QnA.
* [Graphiti](https://github.com/getzep/graphiti): Build Real-Time Knowledge Graphs for AI Agents.
* [Knowledge Graph Builder](https://github.com/neo4j-labs/llm-graph-builder): Neo4j graph construction from unstructured data using LLMs.
* [Wikipedia Knowledge Graph dataset](https://zenodo.org/records/6346900)
* [Wikidata Query Service](https://query.wikidata.org/)
```SPARQL

SELECT DISTINCT ?subjectLabel ?subject ?property ?object 
WHERE {
  VALUES ?subject {wd:Q33002955}
  ?subject ?property ?object .
  SERVICE wikibase:label {
    bd:serviceParam wikibase:language "en" .
    ?subject rdfs:label ?subjectLabel .
  }
}
#defaultView:Graph
```