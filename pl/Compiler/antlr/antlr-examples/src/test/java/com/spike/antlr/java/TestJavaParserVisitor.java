package com.spike.antlr.java;

import com.spike.antlr.TestBase;
import com.spike.antlr.gen.java.JavaLexer;
import com.spike.antlr.gen.java.JavaParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class TestJavaParserVisitor {

    static final String TEST_DATA_BASE_DIR = "src/test/resources/java/";

    static final String TEST_ENUM_DIR = "_enum/";
    static final String TEST_ENUM_CASE1_PATH = TEST_DATA_BASE_DIR + TEST_ENUM_DIR + "ErrorCode1.java";
    static final String TEST_ENUM_CASE2_PATH = TEST_DATA_BASE_DIR + TEST_ENUM_DIR + "ErrorCode2.java";

    static final String test_data_path = TEST_ENUM_CASE2_PATH;

    static JavaLexer lexer;
    static JavaParser parser;
    static JavaParser.CompilationUnitContext context;

    @BeforeClass
    public static void beforeClass() throws IOException {
        Path path = Paths.get(test_data_path);
        CharStream rawCS = CharStreams.fromPath(path);
//        CaseChangingCharStream cs = new CaseChangingCharStream(rawCS, true);
        lexer = new JavaLexer(rawCS);
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        parser = new JavaParser(tokens);

        parser.setErrorHandler(TestBase.ErrorStrategy);
        parser.addErrorListener(new TestBase.MyErrorListener(path));

        context = parser.compilationUnit();
        System.out.println(context.toStringTree(parser));
    }

    @Test
    public void testSimpleJavaParserVisitor() {
        SimpleJavaParserVisitor visitor = new SimpleJavaParserVisitor();
        visitor.visitCompilationUnit(context);
        System.out.println(TestBase.gson.toJson(visitor.rootData));
    }

}
