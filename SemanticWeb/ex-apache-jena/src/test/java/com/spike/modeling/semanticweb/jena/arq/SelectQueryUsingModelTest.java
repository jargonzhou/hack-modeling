package com.spike.modeling.semanticweb.jena.arq;


import com.spike.modeling.semanticweb.jena.Constants;
import com.spike.modeling.semanticweb.jena.util.Models;
import org.apache.jena.query.*;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.RDFNode;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * SPARQL SELECT
 *
 * @author zhoujiagen<br />
 * Jul 5, 2015 5:16:11 PM
 */
public class SelectQueryUsingModelTest {

    // rdf data directory
    private static final String DATA_DIR = "src/main/rdf/";

    // namespace of myfoaf
    private static final String NAMESPACE = "http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl";
    // absolute file path of myfoaf RDF file
    private static final String FILE_PATH = DATA_DIR + "foafData.rdf";

    // the model
    private static Model model = null;

    @BeforeAll
    public static void setUpBeforeClass() {
        // fill the model
        model = Models.fillEmptyModel(NAMESPACE, FILE_PATH);

        assertNotNull(model);
    }

    @AfterAll
    public static void setUpAfterClass() {
        if (model != null) {
            model.close();
        }
    }

    @Test
    public void queryWithSingleVariable() {

        // populate SPARQL SELECT Query string
        StringBuilder sb = new StringBuilder();
        sb.append("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>").append(Constants.NEWLINE);
        sb.append("PREFIX owl: <http://www.w3.org/2002/07/owl#>").append(Constants.NEWLINE);
        sb.append("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>").append(Constants.NEWLINE);
        sb.append("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>").append(Constants.NEWLINE);
        sb.append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(Constants.NEWLINE);
        sb.append("PREFIX myfoaf: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>").append(Constants.NEWLINE);
        sb.append("PREFIX people: <http://www.people.com#>").append(Constants.NEWLINE);
        sb.append("SELECT DISTINCT ?name").append(Constants.NEWLINE);
        sb.append("WHERE { myfoaf:me foaf:name ?name}").append(Constants.NEWLINE);

        // generate Query
        Query query = QueryFactory.create(sb.toString());

        // the binding variable
        String field = "?name";

        // the query result
        String result = null;

        // execute Query
        QueryExecution qexec = QueryExecutionFactory.create(query, model);
        System.out.println("Plan to run SPARQL query: ");
        System.out.println(Constants.BOUNDARY);
        System.out.println(query);
        System.out.println(Constants.BOUNDARY);
        ResultSet rs = qexec.execSelect();
        while (rs.hasNext()) {
            QuerySolution qs = rs.nextSolution();
            RDFNode name = qs.get(field);
            if (name != null) {
                System.out.println(name);
                result = name.toString();
            } else {
                System.out.println("No result!");
            }
        }
        qexec.close();

        // assertion
//		assertEquals("Semantic Web^^http://www.w3.org/2001/XMLSchema#string", result);
        assertEquals("Semantic Web", result);
    }

    @Test
    public void queryWithMultipleVariable() {

        // populate SPARQL SELECT Query string
        StringBuilder sb = new StringBuilder();
        sb.append("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>").append(Constants.NEWLINE);
        sb.append("PREFIX owl: <http://www.w3.org/2002/07/owl#>").append(Constants.NEWLINE);
        sb.append("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>").append(Constants.NEWLINE);
        sb.append("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>").append(Constants.NEWLINE);
        sb.append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(Constants.NEWLINE);
        sb.append("PREFIX myfoaf: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>").append(Constants.NEWLINE);
        sb.append("PREFIX people: <http://www.people.com#>").append(Constants.NEWLINE);
        sb.append("SELECT DISTINCT ?prop ?obj").append(Constants.NEWLINE);
        sb.append("WHERE { myfoaf:me ?prop ?obj}").append(Constants.NEWLINE);

        // generate Query
        Query query = QueryFactory.create(sb.toString());

        // the binding variable
        String prop = "?prop";
        String obj = "?obj";

        int result = 0;

        // execute Query
        QueryExecution qexec = QueryExecutionFactory.create(query, model);
        System.out.println("Plan to run SPARQL query: ");
        System.out.println(Constants.BOUNDARY);
        System.out.println(query);
        System.out.println(Constants.BOUNDARY);
        ResultSet rs = qexec.execSelect();
        while (rs.hasNext()) {
            QuerySolution qs = rs.nextSolution();
            RDFNode propRDFNode = qs.get(prop);
            RDFNode objRDFNode = qs.get(obj);

            System.out.println(propRDFNode + Constants.TAB + objRDFNode);
            result++;
        }
        qexec.close();

        // assertion
        assertTrue(result > 0);
    }

}
