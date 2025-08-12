package com.spike.modeling.semanticweb.jena.util;

import org.apache.jena.query.*;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.sparql.exec.http.QueryExecutionHTTP;

import static com.spike.modeling.semanticweb.jena.Constants.BOUNDARY;
import static com.spike.modeling.semanticweb.jena.Constants.NEWLINE;


/**
 * SPARQL Utilities
 *
 * @author zhoujiagen
 */
public class SPARQLs {
    /**
     * RDF Navigation using SPARQL Query
     *
     * @param model       the RDF model
     * @param query       SPARQL Query String
     * @param queryFields the placeholder of filed in parameter query(sample: ?name)
     */
    public static void query(final Model model, final String query, final String... queryFields) {
        Query q = QueryFactory.create(query);
        QueryExecution qexec = QueryExecutionFactory.create(q, model);
        System.out.println("Plan to run SPARQL query: ");
        System.out.println(BOUNDARY);
        System.out.println(query);
        System.out.println(BOUNDARY);

        ResultSet rs = qexec.execSelect();
        rendererResultSet(rs, queryFields);

        System.out.println(BOUNDARY);

        qexec.close();
    }

    /**
     * RDF Navigation using remote SPARQL Query
     *
     * @param service     the SPARQL end point URL
     * @param query       SPARQL Query String
     * @param queryFields the placeholder of filed in parameter query(sample: ?name)
     * @see <a href="https://jena.apache.org/documentation/query/sparql-remote.html">ARQ - Querying Remote SPARQL Services</a>
     */
    public static void queryRemote(final String service, final String query, String... queryFields) {
        if (queryFields == null || queryFields.length == 0) {
            return;
        }

        QueryExecutionHTTP qexec = QueryExecutionHTTP.service(service).query(query).build();

        System.out.println("Plan to run remote SPARQL query: ");
        System.out.println(BOUNDARY);
        System.out.println(query);
        System.out.println(BOUNDARY);

        ResultSet rs = qexec.execSelect();
        rendererResultSet(rs, queryFields);
        System.out.println(BOUNDARY);


        qexec.close();
    }

    private static void rendererResultSet(ResultSet rs, String... queryFields) {
        System.out.println("Result:");

        ResultSetFormatter.out(rs);

//        int queryFieldSize = queryFields.length;
//        for (int i = 0; i < queryFieldSize; i++) {
//            System.out.print(queryFields[i] + TAB);
//        }
//        System.out.println();
//
//        while (rs.hasNext()) {
//            QuerySolution qs = rs.nextSolution();
//            for (int i = 0; i < queryFieldSize; i++) {
//                RDFNode name = qs.get(queryFields[i]);
//                if (name != null) {
//                    System.out.print(name + TAB);
//                } else {
//                    System.out.print("NULL" + TAB);
//                }
//            }
//            System.out.println();
//        }
    }

    /**
     * generate regular SPARQL Query prefixes
     *
     * @return
     */
    public static StringBuilder getRegualrSPARQLPREFIX() {
        StringBuilder sb = new StringBuilder();
        sb.append("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>").append(NEWLINE)
                .append("PREFIX owl: <http://www.w3.org/2002/07/owl#>").append(NEWLINE)
                .append("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>").append(NEWLINE)
                .append("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>").append(NEWLINE)
        // .append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(NEWLINE)
        // .append("PREFIX myfoaf: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>").append(NEWLINE)
        // .append("PREFIX people: <http://www.people.com#>").append(NEWLINE)
        ;
        return sb;
    }
}
