package com.spike.modeling.semanticweb.jena;

import com.spike.modeling.semanticweb.jena.util.Models;
import com.spike.modeling.semanticweb.jena.util.SPARQLs;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.Resource;
import org.junit.jupiter.api.Test;

/**
 * RDF data manipulation demonstration<br/>
 * <p>
 * Data: FOAF, see <a href="http://xmlns.com/foaf/spec/">FOAF Specification</a>
 * for concrete details
 *
 * @author zhoujiagen
 */
public class RDFDataManipulationTest {
    private static final String ONTOLOGY_DIR = "src/main/rdf/";

    private static final String FOAF_BASE_URI = "http://xmlns.com/foaf/0.1/";
    private static final String FOAF_SCHEMA_FilePath = ONTOLOGY_DIR + "foafSchema.rdf";

    @Test
    public void manipulate() {
        Model model = ModelFactory.createDefaultModel();
        Models.fillModel(model, FOAF_BASE_URI, FOAF_SCHEMA_FilePath);

        // renderer all namespaces
        System.out.println(model.getNsPrefixMap());

        // insert foaf:me rdf:type foaf:Person
        Resource me = model.createResource(FOAF_BASE_URI + "me");
        Property rdfType = model.getProperty(Constants.RDF_TYPE_URL);
        Resource FOAFPersonClass = model.getResource(FOAF_BASE_URI + "Person");
        model.add(me, rdfType, FOAFPersonClass);

        // query the inserted facts
        StringBuilder query = SPARQLs.getRegualrSPARQLPREFIX();
        query.append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(Constants.NEWLINE);
        query.append("SELECT DISTINCT ?person WHERE {?person rdf:type foaf:Person}");
        SPARQLs.query(model, query.toString(), "?person");
    }
}
