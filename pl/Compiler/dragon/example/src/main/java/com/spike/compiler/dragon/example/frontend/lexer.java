package com.spike.compiler.dragon.example.frontend;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import com.spike.compiler.dragon.example.frontend.symbols.Type;

interface lexer {
    class Tag {
        public static final int AND = 256, //
                BASIC = 257, // basic type: int, float, char, bool
                BREAK = 258, //
                DO = 259, //
                ELSE = 260, //
                EQ = 261, //
                FALSE = 262,
                GE = 263, //
                ID = 264, //
                IF = 265, //
                INDEX = 266, // array type, not lexcical token
                LE = 267, //
                MINUS = 268, // not lexcical token
                NE = 269, //
                NUM = 270, //
                OR = 271,
                REAL = 272, //
                TEMP = 273, // not lexcical token
                TRUE = 274, //
                WHILE = 275; //
    }

    class Token {
        public final int tag;

        public Token(int tag) {
            this.tag = tag;
        }

        @Override
        public String toString() {
            return String.valueOf((char) tag);
        }
    }

    class Num extends Token {
        public final int value;

        public Num(int value) {
            super(Tag.NUM);
            this.value = value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }
    }

    // Word manages lexemes for reserved words, identifiers and composite token like
    // '&&'.
    class Word extends Token {
        public String lexeme = "";

        public static final Word and = new Word(Tag.AND, "&&"),
                or = new Word(Tag.OR, "||"),
                eq = new Word(Tag.EQ, "=="),
                ne = new Word(Tag.NE, "!="),
                le = new Word(Tag.LE, "<="),
                ge = new Word(Tag.GE, ">="),
                minus = new Word(Tag.MINUS, "minus"), // -2: minus 2
                True = new Word(Tag.TRUE, "true"),
                False = new Word(Tag.FALSE, "false"),
                temp = new Word(Tag.TEMP, "t");

        public Word(int tag, String lexeme) {
            super(tag);
            this.lexeme = lexeme;
        }

        @Override
        public String toString() {
            return lexeme;
        }
    }

    class Real extends Token {
        public final float value;

        public Real(float value) {
            super(Tag.REAL);
            this.value = value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }
    }

    class Lexer {
        public static int line = 1; // the line number
        private char peek = ' '; // next input character
        private Map<String, Word> words = new HashMap<String, Word>();

        public int line() {
            return line;
        }

        void reserve(Word word) {
            words.put(word.lexeme, word);
        }

        public Lexer() {
            // reserve words
            reserve(new Word(Tag.IF, "if"));
            reserve(new Word(Tag.ELSE, "else"));
            reserve(new Word(Tag.WHILE, "while"));
            reserve(new Word(Tag.DO, "do"));
            reserve(new Word(Tag.BREAK, "break"));
            reserve(Word.True);
            reserve(Word.False);
            reserve(Type.Int); // from symbols
            reserve(Type.Float);
            reserve(Type.Char);
            reserve(Type.Bool);
        }

        // read next input character into 'peek'
        void readch() throws IOException {
            peek = (char) System.in.read();
        }

        boolean readch(char c) throws IOException {
            readch();
            if (peek != c)
                return false;
            peek = ' ';
            return true;
        }

        public Token scan() throws IOException {
            // skip whitespace and record line number
            for (; ; readch()) {
                if (peek == ' ' | peek == '\t')
                    continue;
                else if (peek == '\n')
                    line++;
                else
                    break;
            }

            // recognize composite tokens like '<='
            switch (peek) {
                case '&':
                    if (readch('&'))
                        return Word.and;
                    else
                        return new Token('&');
                case '|':
                    if (readch('|'))
                        return Word.or;
                    else
                        return new Token('|');
                case '=':
                    if (readch('='))
                        return Word.eq;
                    else
                        return new Token('=');

                case '!':
                    if (readch('='))
                        return Word.ne;
                    else
                        return new Token('!');
                case '<':
                    if (readch('='))
                        return Word.le;
                    else
                        return new Token('<');
                case '>':
                    if (readch('='))
                        return Word.ge;
                    else
                        return new Token('>');
            }

            // Num, Real
            if (Character.isDigit(peek)) {
                int v = 0;
                do {
                    v = 10 * v + Character.digit(peek, 10);
                    readch();
                } while (Character.isDigit(peek));
                if (peek != '.')
                    return new Num(v);

                float f = v;
                float d = 10;
                for (; ; ) {
                    readch();
                    if (!Character.isDigit(peek))
                        break;
                    f = f + Character.digit(peek, 10) / d;
                    d = d * 10;
                }
                return new Real(f);
            }

            // id
            if (Character.isLetter(peek)) {
                StringBuilder sb = new StringBuilder();
                do {
                    sb.append(peek);
                    readch();
                } while (Character.isLetterOrDigit(peek));

                String s = sb.toString();
                Word word = words.get(s);
                if (word != null)
                    return word;

                word = new Word(Tag.ID, s);
                words.put(s, word);
                return word;
            }

            // remaing characters as tokens
            Token t = new Token(peek);
            peek = ' ';
            return t;
        }
    }
}
