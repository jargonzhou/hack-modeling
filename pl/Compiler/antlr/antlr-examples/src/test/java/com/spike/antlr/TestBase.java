package com.spike.antlr;

import com.google.common.collect.Maps;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import org.antlr.v4.runtime.*;

import java.nio.file.Path;
import java.util.Map;

public class TestBase {
    static final Map<Path, String> errorMsgCollector = Maps.newHashMap();

    public static ANTLRErrorStrategy ErrorStrategy = new DefaultErrorStrategy() {
    };

    public static class MyErrorListener extends BaseErrorListener {
        private Path path;

        public MyErrorListener(Path path) {
            this.path = path;
        }

        @Override
        public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line,
                                int charPositionInLine, String msg, RecognitionException e) {
            errorMsgCollector.put(path, msg);
        }
    }

    public static Gson gson = new GsonBuilder()
            .setPrettyPrinting()
//            .serializeNulls()
            .create();
}
