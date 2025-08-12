package com.spike.antlr.sql;

import com.spike.antlr.TestBase;
import com.spike.antlr.gen.sql.MySqlLexer;
import com.spike.antlr.gen.sql.MySqlParser;
import com.spike.antlr.gen.sql.MySqlParser.RootContext;
import com.spike.antlr.gen.sql.MySqlParser.SqlStatementsContext;
import com.spike.antlr.gen.sql.MySqlParserVisitor;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 *
 */
public class TestMySqlParserVisitor {

    static String syntax_path = TestConstants.SAMPLE_path;
    static MySqlParser parser;
    static RootContext rootContext;

    @BeforeClass
    public static void beforeClass() throws IOException {
        Path path = Paths.get(syntax_path);
        CharStream rawCS = CharStreams.fromPath(path);
        CaseChangingCharStream cs = new CaseChangingCharStream(rawCS, true);
        MySqlLexer lexer = new MySqlLexer(cs);
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        parser = new MySqlParser(tokens);

        parser.setErrorHandler(TestBase.ErrorStrategy);
        parser.addErrorListener(new TestBase.MyErrorListener(path));

        rootContext = parser.root();
        SqlStatementsContext stmts = rootContext.sqlStatements();
        for (ParseTree stmt : stmts.children) {
            System.out.println(stmt.toStringTree(parser));
        }
    }

    @Test
    public void testSimpleMySqlParserVisitor() {
        MySqlParserVisitor<Void> visitor = new SimpleMySqlParserVisitor();
        visitor.visitRoot(rootContext);
    }

//  @Test
//  public void testRelationalAlgebraMySqlParseVisitor() {
//    MySqlParserVisitor<Object> visitor = new RelationalAlgebraMySqlParserVisitor();
//    SqlStatements roots = (SqlStatements) visitor.visitRoot(rootContext);
//    System.out.print(roots.literal());
//  }
}
