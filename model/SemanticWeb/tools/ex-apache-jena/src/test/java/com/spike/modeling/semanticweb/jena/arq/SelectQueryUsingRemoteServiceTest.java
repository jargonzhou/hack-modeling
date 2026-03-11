package com.spike.modeling.semanticweb.jena.arq;


import com.spike.modeling.semanticweb.jena.Constants;
import org.apache.jena.query.ResultSet;
import org.apache.jena.query.ResultSetFormatter;
import org.apache.jena.sparql.exec.http.QueryExecutionHTTP;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * SPARQL SELECT Query using remote service(SPARQL endpoint)
 *
 * @author zhoujiagen<br />
 * Jul 5, 2015 6:31:30 PM
 * @see <a href="https://www.sparql.org/">SPARQLer</a>
 */
public class SelectQueryUsingRemoteServiceTest {

    private static final String SERVICE_URL = "http://www.sparql.org/sparql";

    @Test
    public void query() {
        // populate SPARQL SELECT Query string
        String query = "PREFIX xsd:     <http://www.w3.org/2001/XMLSchema#>\n" +
                "PREFIX rdf:     <http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n" +
                "PREFIX rdfs:    <http://www.w3.org/2000/01/rdf-schema#>\n" +
                "PREFIX owl:     <http://www.w3.org/2002/07/owl#>\n" +
                "PREFIX fn:      <http://www.w3.org/2005/xpath-functions#>\n" +
                "PREFIX apf:     <http://jena.hpl.hp.com/ARQ/property#>\n" +
                "PREFIX dc:      <http://purl.org/dc/elements/1.1/>\n" +
                "\n" +
                "SELECT ?s ?p ?o\n" +
                "FROM <http://www.w3.org/2002/07/owl>\n" +
                "WHERE\n" +
                "   { ?s ?p ?o }\n" +
                "LIMIT 10";

        // query from remote service
        QueryExecutionHTTP qexec = QueryExecutionHTTP.service(SERVICE_URL).query(query).build();

        System.out.println("Plan to run remote SPARQL query: ");
        System.out.println(Constants.BOUNDARY);
        System.out.println(query);
        System.out.println(Constants.BOUNDARY);

        ResultSet rs = qexec.execSelect();
        assertTrue(rs.hasNext());
        // use result set formatter
        ResultSetFormatter.out(rs);

        qexec.close();
    }
}
