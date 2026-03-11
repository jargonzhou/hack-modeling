package com.spike.compiler.dragon.example.frontend;

import java.util.HashMap;
import java.util.Map;

import com.spike.compiler.dragon.example.frontend.inter.Id;
import com.spike.compiler.dragon.example.frontend.lexer.Tag;
import com.spike.compiler.dragon.example.frontend.lexer.Token;
import com.spike.compiler.dragon.example.frontend.lexer.Word;

interface symbols {
    // Nested map word tokens to inter Id.
    class Env {
        private Map<Token, Id> table;
        protected Env prev; // outer scope

        public Env(Env prev) {
            table = new HashMap<>();
            this.prev = prev;
        }

        public void put(Token token, Id id) {
            table.put(token, id);
        }

        public Id get(Token token) {
            for (Env env = this; env != null; env = env.prev) {
                Id found = env.table.get(token);
                if (found != null)
                    return found;
            }
            return null;
        }
    }

    // Basic type.
    class Type extends Word {
        public int width = 0; // used for storage allocation

        public static final Type Int = new Type("int", Tag.BASIC, 4),
                Float = new Type("float", Tag.BASIC, 8),
                Char = new Type("char", Tag.BASIC, 1),
                Bool = new Type("bool", Tag.BASIC, 1);

        public Type(String name, int tag, int width) {
            super(tag, name);
            this.width = width;
        }

        /// Type conversions.

        public static boolean numeric(Type type) {
            if (Type.Char == type || Type.Int == type || Type.Float == type)
                return true;
            else
                return false;
        }

        public static Type max(Type type1, Type type2) {
            if (!numeric(type1) || !numeric(type2))
                return null;
            else if (Type.Float == type1 || Type.Float == type2)
                return Type.Float;
            else if (Type.Int == type1 || Type.Int == type2)
                return Type.Int;
            else
                return Type.Char;
        }
    }

    // Array Type.
    class Array extends Type {
        public Type of;
        public int size = 1;

        public Array(int size, Type of) {
            super("[]", Tag.INDEX, size * of.width);
            this.size = size;
            this.of = of;
        }

        public String toString() {
            return "[" + size + "] " + of.toString();
        }
    }
}
