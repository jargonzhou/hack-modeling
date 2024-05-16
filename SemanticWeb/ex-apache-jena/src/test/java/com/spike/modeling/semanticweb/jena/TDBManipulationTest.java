package com.spike.modeling.semanticweb.jena;

import com.spike.modeling.semanticweb.jena.util.Models;
import com.spike.modeling.semanticweb.jena.util.SPARQLs;
import org.apache.jena.query.Dataset;
import org.apache.jena.query.ReadWrite;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.tdb1.TDB1Factory;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Jena's TDB HelloWorld
 *
 * @author zhoujiagen
 */
public class TDBManipulationTest {
    private static final Logger logger = LoggerFactory.getLogger(TDBManipulationTest.class);

    private static final String TDB_DIR = "tdb";

    private static final String ONTOLOGY_DIR = "src/main/rdf/";
    private static final String FOAF_BASE_URI = "http://xmlns.com/foaf/0.1/";
    private static final String FOAF_SCHEMA_FilePath = ONTOLOGY_DIR + "foafSchema.rdf";

    @BeforeAll
    public static void beforeAll() {
        // clean the TDB directory
        Models.cleanDirectory(TDB_DIR);
    }

    /**
     * see <a href="http://jena.apache.org/documentation/tdb/assembler.html">TDB
     * Assembler</a> for concrete details
     */
    @Test
    public void demoOfUsingAnAssemblerFile() {
        // Assembler way: Make a TDB-back Jena model in the named directory.
        // This way, you can change the model being used without changing the
        // code.
        // The assembler file is a configuration file.
        // The same assembler description will work in Fuseki.
        String assemblerFile = "src/main/tdb/tdb-assembler.ttl";
        Dataset dataset = TDB1Factory.assembleDataset(assemblerFile); // ...

        // read something
        logger.debug("read tx start!!!");
        demoOfReadTransaction(dataset);
        logger.debug("read tx end!!!");

        // write something
        logger.debug("write tx start!!!");
        demoOfWriteTransaction(dataset);
        logger.debug("write tx end!!!");

        // read again
        logger.debug("read tx start!!!");
        demoOfReadTransaction(dataset);
        logger.debug("read tx end!!!");

        dataset.close();
    }

    @Test
    public void demoOfUsingADirectory() {
        // Make a TDB-backed dataset
        String directory = TDB_DIR;

        // read something
        Dataset dataset = TDB1Factory.createDataset(directory);
        logger.debug("read tx start!!!");
        demoOfReadTransaction(dataset);
        logger.debug("read tx end!!!");
        dataset.close();

        // write something
        dataset = TDB1Factory.createDataset(directory);
        logger.debug("write tx start!!!");
        demoOfWriteTransaction(dataset);
        logger.debug("write tx end!!!");
        dataset.close();

        // read again
        dataset = TDB1Factory.createDataset(directory);
        logger.debug("read tx start!!!");
        demoOfReadTransaction(dataset);
        logger.debug("read tx end!!!");
        dataset.close();
    }

    private static void demoOfReadTransaction(Dataset dataset) {
        dataset.begin(ReadWrite.READ);

        // Get model inside the transaction
        Model model = dataset.getDefaultModel();

        // query the inserted facts
        StringBuilder query = SPARQLs.getRegualrSPARQLPREFIX();
        query.append("PREFIX foaf: <http://xmlns.com/foaf/0.1/>").append(Constants.NEWLINE);
        query.append("SELECT DISTINCT ?person WHERE {?person rdf:type foaf:Person}");
        SPARQLs.query(model, query.toString(), "?person");

        model.close();// closing the model to flush

        dataset.end();
    }

    private static void demoOfWriteTransaction(Dataset dataset) {
        dataset.begin(ReadWrite.WRITE);

        Model model = dataset.getDefaultModel();

        Models.fillModel(model, FOAF_BASE_URI, FOAF_SCHEMA_FilePath);

        // insert foaf:me rdf:type foaf:Person
        Resource me = model.createResource(FOAF_BASE_URI + "me");
        Property rdfType = model.getProperty(Constants.RDF_TYPE_URL);
        Resource FOAFPersonClass = model.getResource(FOAF_BASE_URI + "Person");
        model.add(me, rdfType, FOAFPersonClass);
        // model.write(System.out);// for debug

        model.close();// closing the model to flush

        dataset.commit();

        dataset.end();
    }
}
