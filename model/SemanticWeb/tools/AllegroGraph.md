# AllegroGraph
* https://allegrograph.com/
* https://allegrograph.com/support/

> AllegroGraph is a database and application framework for building Enterprise Knowledge Graph solutions based on a high performance triple store.
> Data and metadata can be managed using [Java, Python, Lisp and HTTP](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#ai-programming) interfaces, and queried using [SPARQL](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#SPARQL) and [Prolog](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#prolog). AllegroGraph comes with [Social Network Analysis](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#sna), [geospatial](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#geospatial), [temporal](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#temporal) and [reasoning](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#reasoning-intro) capabilities.
> [AllegroGraph FedShard](https://franz.com/agraph/support/documentation/current/agraph-introduction.html#Distributed-and-Federated-Repositories)™ is our newest feature offering massive horizontal scalability.

# Setup

```shell
cd /home/zhoujiagen
mkdir -p tmp/ag6.4.2
cd /home/zhoujiagen/agraph-6.4.2
./install-agraph /home/zhoujiagen/tmp/ag6.4.2/
netstat -an | grep 10035
```

```shell
/home/zhoujiagen/tmp/ag6.4.2/bin/agraph-control --config /home/zhoujiagen/tmp/ag6.4.2/lib/agraph.cfg start
/home/zhoujiagen/tmp/ag6.4.2/bin/agraph-control --config /home/zhoujiagen/tmp/ag6.4.2/lib/agraph.cfg stop
```

数据: [中国旅游景点知识图谱](http://openkg.cn/dataset/tourist-attraction)


```sparql
 t: http://www.brain-inspired-cognitive-engine.org/knowledge-engine/cas-kb/
 所属地区
SELECT DISTINCT ?l1 ?l2
WHERE { ?s rdfs:label ?l1.
  ?s t:suoshudiqu ?o.
      ?o rdfs:label ?l2.
}

 实例
SELECT DISTINCT ?sl ?ol
WHERE {
?s rdfs:label ?sl.
  ?o t:shili ?s. # techan
  ?o rdfs:label ?ol
}
```


# Architecture
![Architecture](https://franz.com/agraph/support/documentation/current/ag-arch.png)

# Usage
```
 https://trello.com/c/4hloexWe/26-allegrograph

/home/zhoujiagen/tmp/ag6.4.2/bin/agraph-control --config /home/zhoujiagen/tmp/ag6.4.2/lib/agraph.cfg start
/home/zhoujiagen/tmp/ag6.4.2/bin/agraph-control --config /home/zhoujiagen/tmp/ag6.4.2/lib/agraph.cfg stop
```

Play with [sparql-kernel](https://github.com/paulovn/sparql-kernel)

```
pip install sparqlkernel
jupyter sparqlkernel install

%endpoint http://192.168.56.110:10035/repositories/demo-sparql
%auth basic zhoujiagen zhoujiagen

PREFIX foaf:    <http://xmlns.com/foaf/0.1/>
SELECT ?nameX ?nameY ?nickY
WHERE
  { ?x foaf:knows ?y ;
       foaf:name ?nameX .
    ?y foaf:name ?nameY .
    OPTIONAL { ?y foaf:nick ?nickY }
  }

```

# See Also
* [Gruff: A Triple-Store Browser, Query Manager, and Editor](https://franz.com/agraph/support/documentation/current/gruff.html)