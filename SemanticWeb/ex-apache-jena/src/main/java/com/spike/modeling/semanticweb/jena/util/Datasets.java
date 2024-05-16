package com.spike.modeling.semanticweb.jena.util;

import org.apache.commons.lang3.StringUtils;
import org.apache.jena.query.Dataset;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.tdb.TDBFactory;

/**
 * RDF data set utilities
 *
 * @author zhoujiagen<br />
 * Jul 5, 2015 5:52:54 PM
 */
public class Datasets {

    /**
     * get default model of dataset
     *
     * @param dataset
     * @return
     */
    public static final Model getDefaultModel(Dataset dataset) {
        if (dataset == null) {
            return null;
        }

        return dataset.getDefaultModel();
    }

    /**
     * get default model from dataset specified by a assembler file
     *
     * @param assembleFilePath
     * @return
     */
    public static final Model getDefaultModelFromAssembler(String assembleFilePath) {
        if (StringUtils.isBlank(assembleFilePath)) {
            return null;
        }

        // create dataset using assembler file
        Dataset dataset = TDBFactory.assembleDataset(assembleFilePath);
        if (dataset == null) {
            return null;
        }

        return getDefaultModel(dataset);
    }

    /**
     * get default model from dataset specified by directory path
     *
     * @param directory
     * @return
     */
    public static final Model getDefaultModelFromDirectory(String directory) {
        if (StringUtils.isBlank(directory)) {
            return null;
        }

        // create dataset using directory path
        Dataset dataset = TDBFactory.createDataset(directory);
        if (dataset == null) {
            return null;
        }

        return getDefaultModel(dataset);
    }

}
