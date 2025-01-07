//package com.spike.javacc.java15;
//
//import java.io.FileNotFoundException;
//import java.io.Reader;
//import java.io.StringReader;
//
//public class Java15Main {
//    public static void main(String[] args) throws FileNotFoundException {
//        Reader r = new StringReader(wrong);
//        JavaParser p = new JavaParser(r);
//        try {
//            p.CompilationUnit();
//        } catch (ParseException e) {
//            e.printStackTrace();
//        }
//    }
//
//    static final String input = "package com.spike.javacc.java15;\n" +
//            "\n" +
//            "// for Java1.5.jj\n" +
//            "public class MyToken extends Token\n" +
//            "{\n" +
//            "  /**\n" +
//            "   * Constructs a new token for the specified Image and Kind.\n" +
//            "   */\n" +
//            "  public MyToken(int kind, String image)\n" +
//            "  {\n" +
//            "     this.kind = kind;\n" +
//            "     this.image = image;\n" +
//            "  }\n" +
//            "\n" +
//            "  int realKind = JavaParserConstants.GT;\n" +
//            "\n" +
//            "  /**\n" +
//            "   * Returns a new Token object.\n" +
//            "  */\n" +
//            "\n" +
//            "  public static final Token newToken(int ofKind, String tokenImage)\n" +
//            "  {\n" +
//            "    return new MyToken(ofKind, tokenImage);\n" +
//            "  }\n" +
//            "}";
//
//    static final String wrong = "package com.spike.javacc.java15;\n" +
//            "\n" +
//            "// for Java1.5.jj\n" +
//            "public MyToken extends Token\n" + // no 'class'
//            "{\n" +
//            "  /**\n" +
//            "   * Constructs a new token for the specified Image and Kind.\n" +
//            "   */\n" +
//            "  public MyToken(int kind, String image)\n" +
//            "  {\n" +
//            "     this.kind = kind;\n" +
//            "     this.image = image;\n" +
//            "  }\n" +
//            "\n" +
//            "  int realKind = JavaParserConstants.GT;\n" +
//            "\n" +
//            "  /**\n" +
//            "   * Returns a new Token object.\n" +
//            "  */\n" +
//            "\n" +
//            "  public static final Token newToken(int ofKind, String tokenImage)\n" +
//            "  {\n" +
//            "    return new MyToken(ofKind, tokenImage);\n" +
//            "  }\n" +
//            "}";
//}
