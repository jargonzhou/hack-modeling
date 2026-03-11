package com.spike.modeling.semanticweb.jena.util;

import com.spike.modeling.semanticweb.jena.Constants;
import org.apache.jena.fuseki.main.FusekiServer;
import org.apache.jena.query.DatasetFactory;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.riot.RDFDataMgr;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.InputStream;

public class SPARQLsTest {

    @BeforeAll
    public static void beforeAll() {
        // https://jena.apache.org/documentation/fuseki2/fuseki-embedded.html
        Model model = ModelFactory.createDefaultModel();
        InputStream is = RDFDataMgr.open("src/main/rdf/foafData.rdf");
        model.read(is, "http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl");
        FusekiServer server = FusekiServer.create()
                .port(3030)
                .add("/ds", DatasetFactory.create(model))
                .build();
        server.start();
    }

    /**
     * Caution: the service is site on a Fuseki running on local tomcat7.0
     */
    @Test
    public void queryRemote() {
        final String service = "http://localhost:3030/ds/query";

        String query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>" +
                Constants.NEWLINE +
                "PREFIX owl: <http://www.w3.org/2002/07/owl#>" +
                Constants.NEWLINE +
                "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>" +
                Constants.NEWLINE +
                "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>" +
                Constants.NEWLINE +
                "PREFIX hw: <http://blog.sina.com.cn/zhoujiagenontology/helloworld.owl#>" +
                Constants.NEWLINE +
                "SELECT ?predicate ?object " +
                Constants.NEWLINE +
                "WHERE {   hw:me ?predicate ?object }" +
                Constants.NEWLINE +
                "LIMIT 25";

        SPARQLs.queryRemote(service, query, "?predicate", "?object");
    }
}
