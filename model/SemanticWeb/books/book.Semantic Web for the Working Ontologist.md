# Semantic Web for the Working Ontologist
* Allemang, Dean / Hendler, Jim / Gandon, Fabien. **Semantic Web for the Working Ontologist: Effective Modeling for Linked Data, RDFS, and OWL**. 2020, 3. edition.

# 1 What Is the Semantic Web?
- The AAA slogan: Anyone can say Anything about Any topic.
- Open World/Closed World
- Nonunique namming
- The network effect
- The data wilderness

# 2 Semantic Modeling
- modeling
- formality/informality
- commonality and variability
- expressivity

# 3 RDF—The Basis of the Semantic Web
- RDF(Resource Description Framework)
- Triple
- Graph
- Merging
- URI(Uniform Resource Indicator)
- namespace
- CURIE: abbreviated version of a URI, made up of a namespace identifier and a name, separated by a colon
- `rdf:type`
- `rdf:Property`
- Reification: making a statement abount another statement
	- `rdf:subject`, `rdf:predicate`, `rdf:object`
- N-Triples, Turtle, RDF/XML
- Blank nodes

alternative for serialization:
- N-Triples
- Turtle/N3
	- [RDF 1.1 Turtle](https://www.w3.org/TR/2014/REC-turtle-20140225/)
	- [RDF 1.1 N-Triples](https://www.w3.org/TR/2014/REC-n-triples-20140225/)
	- In this book, we use a more compact serialization of RDF called Turtle which is itself a subset of a syntax called N3
	- Turtle provides some abbreviations to improve terseness and readability; in this book, we use just a few of these. 
		- `a`
- RDF/XML
- JSON-LD
serializable triples for use with named graphs:
- N-Quads
- TriG: extension of Turtle

```n-triples
mfg : Product1 rdf: type mfg: Product .
lit : Shakespeare rdf: type lit: Playwright .

# abbreviation: a
mfg : Product1 a mfg: Product .
lit : Shakespeare a lit: Playwright .
```
# 4 Semantic Web Application Architecture
- RDF parser/serializer
- RDF store
- RDF query engine
- SPARQL
- SPARQL endpoint
- Application interface
- Converter
- RDFa: standard for encoding and retrieving RDF metadata from HTML pages.

embed RDF data into an HTML web page:
- Microdata: Schema.org
- RDFs: W3C
- JSON-LD
- [[Linked Data Structured Data on The Web[Manning, 2014].pdf]]

# 5 Linked Data 
- HTTP URI
- dereferencing
- content negotiation
- LDF(Linked Data Platform)

# 6 Querying the Semantic Web—SPARQL
- graph pattern
- variables
- `SELECT` query
- `CONSTRUCT` queru
- queries and rules
- federated query

# 7 Extending RDF: RDFS and SCHACL
- inferencing
- asserted triples
- inferred triples
- inference rules
- inference engine
- SHACL shapes to validate RDF data at the structural level by prodving the constraint.

# 8 RDF Schema 
- `rdfs:subClassOf`
- `rdfs:subPropertyOf`
- `rdfs:domain`, `rdfs:range`
- logical operation in RDFS: union, intersection, ...

# 9 RDFS-Plus 
- `rdfs:subClassOf`, `rdfs:subPropertyOf`
- `rdfs:doman`, `rdfs:range`
- annotation properties
	- `rdfs:label`
	- `rdfs:comment`
- OWL equality
	- `equicalentClass`
	- `equivalentProperty`
	- `sameAs`
- OWL property characteristics
	- `inverseOf`
	- `TransitiveProperty`
	- `SymmetricProperty`
	- `FunctionProperty`
	- `InverseFunctionalProperty`
	- `ObjectProperty`
	- `DatatypeProperty`


# 10 Using RDFS-Plus in the Wild 
- Data.gov
- FOAF: Friend of a Friend
- metamodeling
- RDFa
- OGP(Open Graph Protocol): let Facebook users link to pages outside of Facebook

# 11 SKOS—Managing Vocabularies with RDFS-Plus
- controlled vocabulary
- SKOS(Simple Knowledge Organization System)
- AGROVOC: UN argiculture vocabulary
- NAL: National Agriculture Library

# 12 Basic OWL 
- `owl:Restriction`
- `owl:hasValue`
- `owl:someValuesFrom`
- `owl:allValuesFrom`
- `owl:onProperty`

# 13 Counting and Sets in OWL 
- `owl:unionOf`, `owl:intersectionOf`, `owl:complementOf`
- Open World Assumption
- `owl:oneOf`
- `owl:differentFrom`
- `owl:disjointWith`
- `owl:AllDisjointClasses`
- `owl:cardinality`, `owl:minCardinality`, `owl:maxCardinality`
- contradiction
- satisfiability, unsatisfiability

# 14 Ontologies on the Web—Putting It All Together
- `owl:imports`
- Ontology Design Patterns
- Good Relations
- QUDT: Quantities, Units, Dimensions, Types
- OBO: Open Biological and Biomedical Ontologies
- CHEBI: Chemical of Biological Interests

# 15 Good and Bad Modeling Practices
- Then Semantic Web assumptions: AAA, Open World, Nonunique Naming
- inferencing
- competency questions
- completeness
- specificity
- granularity
- formality
- reusability
- modeling for variability
- modeling for reuse
- wishful naming
- model testing

# 16 Expert Modeling in OWL
- OWL: Web Ontology Langauge
- OWL 2 DL: ensure decidability
- OWL 2 EL: improve computational complexity
- OWL 2 RL: compatible with Rules processors
- OWL 2 QL: compatible with database queries
- RIF: Rule Interchange Format
- metamodeling
- multipart properties
- multiple inverse functional properties
# 17 Conclusions and Future Work
