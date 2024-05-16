package com.spike.modeling.semanticweb.jena.arq;


import com.spike.modeling.semanticweb.jena.Constants;
import org.apache.jena.query.*;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;


/**
 * SPARQL SELECT Query using a dataset which contains multiple models
 *
 * @author zhoujiagen<br />
 * Jul 5, 2015 6:00:56 PM
 */
public class SelectQueryUsingDatasetTest {

    private static Dataset dataset = null;

    @BeforeAll
    public static void setUpBeforeClass() {
        String dftGraphURI = "http://www.w3.org/People/Berners-Lee/card#";
        List<String> namedGraphURIs = new ArrayList<String>();
//		namedGraphURIs.add("http://www.koalie.net/foaf.rdf");
        // error
        // namedGraphURIs.add("http://heddley.com/edd/foaf.rdf");
        // 404
        // namedGraphURIs.add("http://www.cs.umd.edu/~hendler/2003/foaf.rdf");
//		namedGraphURIs.add("http://www.dajobe.org/foaf.rdf");
//		namedGraphURIs.add("http://www.isi.edu/~gil/foaf.rdf");
//		namedGraphURIs.add("http://www.ivan-herman.net/foaf.rdf");
//		namedGraphURIs.add("http://www.kjetil.kjernsmo.net/foaf");
//		namedGraphURIs.add("http://www.lassila.org/ora.rdf");
        // no response
        // namedGraphURIs.add("http://www.mindswap.org/2004/owl/mindswappers");

        dataset = DatasetFactory.create(dftGraphURI, namedGraphURIs);

        assertNotNull(dataset);
    }

    @Test
    public void query() {
        // populate SPARQL SELECT Query string
        String sb = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>" + Constants.NEWLINE +
                "PREFIX owl: <http://www.w3.org/2002/07/owl#>" + Constants.NEWLINE +
                "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>" + Constants.NEWLINE +
                "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>" + Constants.NEWLINE +
                "PREFIX foaf: <http://xmlns.com/foaf/0.1/>" + Constants.NEWLINE +
                "PREFIX myfoaf: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>" + Constants.NEWLINE +
                "PREFIX people: <http://www.people.com#>" + Constants.NEWLINE +
                "SELECT *" + Constants.NEWLINE +
                "WHERE {" + Constants.NEWLINE +
                "		GRAPH ?originGraph {" + Constants.NEWLINE +
                " 			_:blank1 foaf:knows _:blank2." + Constants.NEWLINE +
                "				_:blank2 rdf:type foaf:Person;" + Constants.NEWLINE +
                "							foaf:nick ?nickname;" + Constants.NEWLINE +
                "							foaf:name ?realname" + Constants.NEWLINE +
                "		}" + Constants.NEWLINE +
                "}" + Constants.NEWLINE;

        // generate Query
        Query query = QueryFactory.create(sb);

        // the binding variable
        // String originGraph = "?originGraph";
        // String nickname = "?nickname";
        // String realname = "?realname";

        // the query result
        // int result = 0;

        // execute Query using dataset
        QueryExecution qexec = QueryExecutionFactory.create(query, dataset);
        System.out.println("Plan to run SPARQL query: ");
        System.out.println(Constants.BOUNDARY);
        System.out.println(query);
        System.out.println(Constants.BOUNDARY);
        ResultSet rs = qexec.execSelect();

        // while (rs.hasNext()) {
        // QuerySolution qs = rs.nextSolution();
        // RDFNode originGraphNode = qs.get(originGraph);
        // RDFNode nicknameNode = qs.get(nickname);
        // RDFNode realnameNode = qs.get(realname);
        //
        // System.out.println(originGraphNode + TAB + nicknameNode + TAB +
        // realnameNode);
        //
        // }

        // use result set formatter
        ResultSetFormatter.out(rs, query);

        qexec.close();
    }
}
