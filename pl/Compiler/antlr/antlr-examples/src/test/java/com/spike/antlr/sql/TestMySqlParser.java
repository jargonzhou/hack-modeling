package com.spike.antlr.sql;

import com.spike.antlr.TestBase;
import com.spike.antlr.gen.sql.MySqlLexer;
import com.spike.antlr.gen.sql.MySqlParser;
import com.spike.antlr.gen.sql.MySqlParser.RootContext;
import com.spike.antlr.gen.sql.MySqlParser.SqlStatementsContext;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * <p>
 * grammar: https://github.com/antlr/grammars-v4/tree/master/mysql
 * <p>
 * 注意文法中SQL关键字是大写的, 使用{@link CaseChangingCharStream}预处理.
 */
public class TestMySqlParser {


    public static void main(String[] args) throws IOException {

        Path path = Paths.get(TestConstants.all_path);
        CharStream rawCS = CharStreams.fromPath(path);
        CaseChangingCharStream cs = new CaseChangingCharStream(rawCS, true);
        MySqlLexer lexer = new MySqlLexer(cs);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        MySqlParser parser = new MySqlParser(tokens);

        parser.setErrorHandler(TestBase.ErrorStrategy);
        parser.addErrorListener(new TestBase.MyErrorListener(path));

        // ParseTree tree = parser.root();
        // System.out.println(tree.toStringTree(parser));
        RootContext rootContext = parser.root();
        SqlStatementsContext stmts = rootContext.sqlStatements();
        for (ParseTree stmt : stmts.children) {
            System.out.println(stmt.toStringTree(parser));
        }
    }
}
