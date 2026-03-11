package com.spike.modeling.semanticweb.jena;

import org.apache.jena.query.*;
import org.apache.jena.rdf.model.*;
import org.apache.jena.reasoner.Reasoner;
import org.apache.jena.reasoner.ReasonerRegistry;
import org.apache.jena.reasoner.rulesys.GenericRuleReasoner;
import org.apache.jena.reasoner.rulesys.Rule;
import org.apache.jena.riot.RDFDataMgr;

import java.io.IOException;
import java.io.InputStream;

import static com.spike.modeling.semanticweb.jena.Constants.*;

/**
 * Semantic Programming HelloWorld<br/>
 * <p>
 * All RDF files except "foafSchema.rdf" are generate using Protege
 *
 * @author zhoujiagen
 */
public class HelloSemanticWeb {
    private static final String ONTOLOGY_DIR = "src/main/rdf/";

    // namespace of FOAF
    private static final String FOAF_NS = "http://xmlns.com/foaf/0.1/";
    // absolute file path of FOAF RDF file
    private static final String FOAF_SCHEMA_FN = ONTOLOGY_DIR + "foafSchema.rdf";

    // namespace of my foaf
    private static final String MYFOAF_NS = "http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl";
    // absolute file path of myfoaf RDF file
    private static final String MYFOAF_DATA_FN = ONTOLOGY_DIR + "foafData.rdf";

    // namespace of people
    private static final String PEOPLE_NS = "http://www.people.com";
    // absolute file path of people file
    private static final String PEOPLE_SCHEMA_FN = ONTOLOGY_DIR + "peopleSchema.rdf";
    private static final String PEOPLE_DATA_FN = ONTOLOGY_DIR + "peopleData.rdf";

    // Jena's RDF Model
    private static Model friendsModel = null;
    // Schema Model of all ontology: the TBox
    private static Model schema = null;

    // Jena's Inference Model
    private static InfModel inferredModel = null;

    public static void main(String[] args) throws IOException {
        version1();

//        version2();

//        version3();
    }

    /**
     * version 1: rdf navigate using sparql query
     */
    public static void version1() throws IOException {
        System.out.println("Load my FOAF friends");
        friendsModel = populateMyFOAFFriends(MYFOAF_DATA_FN);

        System.out.println("Say Hello to myself");
        sayHelloToMyself(friendsModel);

        System.out.println("Say Hello to my friends");
        sayHelloToMyFriends(friendsModel);
    }

    /**
     * version 2: ontology integration using alignment
     */
    public static void version2() throws IOException {
        System.out.println("Load the data");
        loadABox();

        System.out.println("Generate the schema to contain all ontology's tbox");
        loadTBox();

        // ontology alignment
        alignmentInTBox();

        // bind OWL reasoner
        bindReasoner();

        // execute SPARQL query
        sayHelloToMyself(inferredModel);
        sayHelloToMyFriends(inferredModel);
    }

    /**
     * version 3: using jena rules
     */
    public static void version3() throws IOException {
        System.out.println("Load the data");
        loadABox();

        System.out.println("Generate the schema to contain all ontology's tbox");
        loadTBox();

        // ontology alignment
        alignmentInTBox();

        // bind rule reasoner
        bindJenaRuleReasoner();

        // execute SPARQL query
        sayHelloToGmailFriends(inferredModel);
    }

    private static void bindJenaRuleReasoner() {
        final String rule = "[gmailFriend: (?person <http://xmlns.com/foaf/0.1/mbox_sha1sum> ?email), strConcat(?email, ?lit), regex(?lit, '(.*gmail.com)')"
                + "-> (?person " + RDF_TYPE_INSPARQL + " <http://www.people.com#GmailPerson>)]";
        Reasoner ruleReasoner = new GenericRuleReasoner(Rule.parseRules(rule));
        ruleReasoner = ruleReasoner.bindSchema(schema);
        inferredModel = ModelFactory.createInfModel(ruleReasoner, friendsModel);
    }

    /**
     * load all ontologies' ABox
     */
    private static void loadABox() {
        friendsModel = ModelFactory.createDefaultModel();
        InputStream is = RDFDataMgr.open(MYFOAF_DATA_FN);// MyFOAF ABox
        friendsModel.read(is, MYFOAF_NS);

        is = RDFDataMgr.open(PEOPLE_DATA_FN);// people ABox
        friendsModel.read(is, PEOPLE_NS);
    }

    /**
     * Load all ontologies' TBox
     */
    private static void loadTBox() {
        schema = ModelFactory.createDefaultModel();
        InputStream is = RDFDataMgr.open(FOAF_SCHEMA_FN);// FOAF TBox
        schema.read(is, FOAF_NS);

        is = RDFDataMgr.open(PEOPLE_SCHEMA_FN);// people TBox
        schema.read(is, PEOPLE_NS);
    }

    /**
     * Ontology Alignment: TBox
     */
    private static void alignmentInTBox() {
        // [1]people:Individual = foaf:Person
        Resource resource = schema.createResource(PEOPLE_NS + "#Individual");
        Property property = schema.createProperty(OWL_URL + "equivalentClass");
        Resource object = schema.createResource(FOAF_URL + "Person");
        schema.add(resource, property, object);

        // [2]people:hasName = foaf:name
        resource = schema.createResource(PEOPLE_NS + "#hasName");
        property = schema.createProperty(OWL_URL + "equivalentProperty");
        object = schema.createResource(FOAF_URL + "name");
        schema.add(resource, property, object);

        // [3]people:hasFriend < foaf:knows
        resource = schema.createResource(PEOPLE_NS + "#hasFriend");
        property = schema.createProperty(RDFS_URL + "subPropertyOf");
        object = schema.createResource(FOAF_URL + "knows");
        schema.add(resource, property, object);

        // [4]myfoaf:me = people:individual_5
        resource = schema.createResource(MYFOAF_NS + "#me");
        property = schema.createProperty(OWL_URL + "sameAs");
        object = schema.createResource(PEOPLE_NS + "#individual_5");
        schema.add(resource, property, object);
    }

    private static void bindReasoner() {
        Reasoner reasoner = ReasonerRegistry.getOWLReasoner();
        reasoner = reasoner.bindSchema(schema);// tbox
        inferredModel = ModelFactory.createInfModel(reasoner, friendsModel);// abox
    }

    /**
     * fill model using files
     *
     * @param base     the namespace
     * @param filePath the RDF file absolute path
     * @return model
     */
    private static Model fillModel(String base, String filePath) throws IOException {
        Model model = ModelFactory.createDefaultModel();
        InputStream is = RDFDataMgr.open(filePath);
        model.read(is, base);
        is.close();
        return model;
    }

    /**
     * fill the FOAF model
     *
     * @param filePath model file path
     * @return model
     */
    private static Model populateMyFOAFFriends(String filePath) throws IOException {
        return fillModel(MYFOAF_NS, filePath);
    }

    /**
     * RDF Model navigation using SPARQL Query: my name
     *
     * @param model the model
     */
    private static void sayHelloToMyself(Model model) {
        String query = generateMyselfSPARQLQuery();
        sparql(model, query, "?name");
    }

    private static void sayHelloToGmailFriends(Model model) {
        String query = generateGmailFriendsSPARQLQuery();
        sparql(model, query, "?name");
    }

    /**
     * RDF Model navigation using SPARQL Query: friends' names
     *
     * @param model the model
     */
    private static void sayHelloToMyFriends(Model model) {
        String query = generateFriendsSPARQLQuery();
        sparql(model, query, "?name");
    }

    /**
     * RDF Navigation using SPARQL Query
     *
     * @param model the RDF model
     * @param query SPARQL Query String
     * @param field the placeholder of filed in parameter query
     */
    private static void sparql(Model model, String query, String field) {
        Query q = QueryFactory.create(query);
        QueryExecution execution = QueryExecutionFactory.create(q, model);
        System.out.println("Plan to run SPARQL query: ");
        System.out.println(BOUNDARY);
        System.out.println(query);
        System.out.println(BOUNDARY);
        ResultSet rs = execution.execSelect();
        while (rs.hasNext()) {
            QuerySolution qs = rs.nextSolution();
            RDFNode name = qs.get(field);// using RDFNode currently
            if (name != null) {
                System.out.println("Hello to " + name);
            } else {
                System.out.println("No friends found!");
            }
        }
        execution.close();
    }

    private static String generateMyselfSPARQLQuery() {
        StringBuilder sb = generateSPARQLPREFIX();
        // append query statement
        sb.append("SELECT DISTINCT ?name").append(NEWLINE).append("WHERE { myfoaf:me foaf:name ?name}").append(NEWLINE);
        return sb.toString();
    }

    private static String generateGmailFriendsSPARQLQuery() {
        StringBuilder sb = generateSPARQLPREFIX();
        sb.append("SELECT DISTINCT ?name WHERE {?name rdf:type people:GmailPerson}");
        return sb.toString();
    }

    private static String generateFriendsSPARQLQuery() {
        StringBuilder sb = generateSPARQLPREFIX();
        sb.append("SELECT DISTINCT ?name").append(NEWLINE).append("WHERE { myfoaf:me foaf:knows ?friend. ")
                .append("?friend foaf:name ?name}").append(NEWLINE);
        return sb.toString();
    }

    /**
     * @return SPARQL Query prefixes
     */
    private static StringBuilder generateSPARQLPREFIX() {
        StringBuilder sb = new StringBuilder();
        sb.append("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>").append(NEWLINE)
                .append("PREFIX owl: <http://www.w3.org/2002/07/owl#>").append(NEWLINE)
                .append("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>").append(NEWLINE)
                .append("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>").append(NEWLINE)
                .append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(NEWLINE)
                .append("PREFIX myfoaf: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>").append(NEWLINE)
                .append("PREFIX people: <http://www.people.com#>").append(NEWLINE);
        return sb;
    }
}
