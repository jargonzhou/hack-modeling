package com.spike.modeling.semanticweb.jena.util;

import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.util.FileManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.InputStream;
import java.nio.file.Path;
import java.nio.file.Paths;


/**
 * {@link Model} utilities
 *
 * @author zhoujiagen
 */
public class Models {
    private static final Logger logger = LoggerFactory.getLogger(Models.class);

    /**
     * Fill model using a file
     *
     * @param model    the filled model, NOT NULL
     * @param base     the base uri
     * @param filePath the file's absolute path
     */
    public static final void fillModel(Model model, String base, String filePath) {
        if (null == model) {
            return;
        }

        try (InputStream is = FileManager.get().open(filePath)) {
            model.read(is, base);
        } catch (Exception e) {
            logger.error("fillModel failed, refer", e);
        }
    }

    /**
     * create a model from RDF file
     *
     * @param base     the base uri
     * @param filePath the file's absolute path
     * @return
     */
    public static final Model fillEmptyModel(String base, String filePath) {
        Model model = ModelFactory.createDefaultModel();

        try (InputStream is = FileManager.get().open(filePath)) {
            model.read(is, base);
        } catch (Exception e) {
            logger.error("fillEmptyModel failed, refer", e);
        }

        return model;
    }

    /**
     * empty a directory
     *
     * @param dirPath
     */
    public static final void cleanDirectory(String dirPath) {
        Path dir = Paths.get(dirPath);
        File[] childFiles = dir.toFile().listFiles();
        if (childFiles != null) {
            for (File child : childFiles) {
                child.delete();
            }
            logger.debug("cleaned " + childFiles.length + " files");
        }
    }
}
