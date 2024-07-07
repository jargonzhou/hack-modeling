package com.spike.compiler.dragon.example.frontend;

import com.spike.compiler.dragon.example.frontend.lexer.Lexer;
import com.spike.compiler.dragon.example.frontend.lexer.Token;
import com.spike.compiler.dragon.example.frontend.lexer.Word;
import com.spike.compiler.dragon.example.frontend.lexer.Num;
import com.spike.compiler.dragon.example.frontend.lexer.Tag;
import com.spike.compiler.dragon.example.frontend.symbols.Array;
import com.spike.compiler.dragon.example.frontend.symbols.Type;

interface inter {
    // Node in syntax tree.
    class Node {
        int lexline = 0; // source line number of the construct at node
        static int labels = 0; // labels counter

        Node() {
            lexline = Lexer.line;
        }

        void error(String s) {
            throw new Error("near line " + lexline + ": " + s);
        }

        /// Emit three-address code.

        public int newlabel() {
            return ++labels;
        }

        public void emitlabel(int i) {
            System.out.print("L" + i + ":");
        }

        public void emit(String s) {
            System.out.println("\t" + s);
        }
    }

    // ---------------------------------------------------------------------------
    // Expressions
    // ---------------------------------------------------------------------------

    // Expressions.
    class Expr extends Node {
        public Token op; // operator
        public Type type;

        public Expr(Token op, Type type) {
            this.op = op;
            this.type = type;
        }

        // Return a term that can fit RHS of a three-address instruction.
        public Expr gen() {
            return this; // in case of address
        }

        // Compute/Reduce an expression down to a signle address.
        public Expr reduce() {
            return this; // in case of address
        }

        /// Generate jumping code for boolean expressions.

        // Jumping code for boolean expression: two labels t and f.
        public void jumping(int t, int f) {
            emitjumps(toString(), t, f);
        }

        public void emitjumps(String test, int t, int f) {
            if (t != 0 && f != 0) {
                emit("if " + test + " goto L" + t);
                emit("goto L" + f);
            } else if (t != 0)
                emit("if " + test + " goto L" + t);
            else if (f != 0)
                emit("iffalse " + test + " goto L" + f);
            else
                ; // nothing
        }

        public String toString() {
            return op.toString();
        }
    }

    // Identifier.
    class Id extends Expr {
        public int offset; // relative address

        public Id(Word id, Type type, int offset) {
            super(id, type);
            this.offset = offset;
        }
    }

    // Provide 'reduce' implementation for 'Arith', 'Unary', 'Access'.
    class Op extends Expr {
        public Op(Token op, Type type) {
            super(op, type);
        }

        @Override
        public Expr reduce() {
            Expr x = gen();
            Temp t = new Temp(type);
            emit(t.toString() + " = " + x.toString());
            return t;
        }
    }

    // Typed temporary.
    class Temp extends Expr {
        static int count = 0;
        int number = 0;

        public Temp(Type type) {
            super(Word.temp, type);
            number = ++count;
        }

        @Override
        public String toString() {
            return "t" + number;
        }
    }

    // Binary operator like '+' and '*'.
    class Arith extends Op {
        public Expr expr1, expr2;

        public Arith(Token op, Expr expr1, Expr expr2) {
            super(op, null);
            this.expr1 = expr1;
            this.expr2 = expr2;
            type = Type.max(expr1.type, expr2.type);
            if (type == null)
                error("type error");
        }

        @Override
        public Expr gen() {
            return new Arith(op, expr1.reduce(), expr2.reduce());
        }

        @Override
        public String toString() {
            return expr1.toString() + " " + op.toString() + " " + expr2.toString();
        }
    }

    // One-operand operator.
    class Unary extends Op {
        public Expr expr;

        public Unary(Token op, Expr expr) {
            super(op, null);
            this.expr = expr;
            type = Type.max(Type.Int, expr.type);
            if (type == null)
                error("type error");
        }

        @Override
        public Expr gen() {
            return new Unary(op, expr.reduce());
        }

        @Override
        public String toString() {
            return op.toString() + " " + expr.toString();
        }
    }

    // Constant.
    class Constant extends Expr {
        public static final Constant True = new Constant(Word.True, Type.Bool),
                False = new Constant(Word.False, Type.Bool);

        public Constant(Token token, Type type) {
            super(token, type);
        }

        public Constant(int i) {
            super(new Num(i), Type.Int);
        }

        @Override
        public void jumping(int t, int f) {
            if (True == this && t != 0)
                emit("goto L" + t);
            else if (False == this && f != 0)
                emit("goto L" + f);
        }
    }

    // Logical expression: Or, And, Not.
    class Logical extends Expr {
        public Expr expr1, expr2;

        Logical(Token op, Expr expr1, Expr expr2) {
            super(op, null);
            this.expr1 = expr1;
            this.expr2 = expr2;
            type = check(expr1.type, expr2.type);
            if (type == null)
                error("type error");
        }

        public Type check(Type type1, Type type2) {
            if (Type.Bool == type1 && Type.Bool == type2)
                return Type.Bool;
            else
                return null;
        }

        @Override
        public Expr gen() {
            int f = newlabel();
            int a = newlabel();
            Temp temp = new Temp(type);
            this.jumping(0, f);
            emit(temp.toString() + " = true");
            emit("goto L" + a);
            emitlabel(f);
            emit(temp.toString() + " = false");
            emitlabel(a);
            return temp;
        }

        @Override
        public String toString() {
            return expr1.toString() + " " + op.toString() + " " + expr2.toString();
        }
    }

    class Or extends Logical {
        public Or(Token op, Expr expr1, Expr expr2) {
            super(op, expr1, expr2);
        }

        @Override
        public void jumping(int t, int f) {
            int label = t != 0 ? t : newlabel();
            expr1.jumping(label, 0);
            expr2.jumping(t, f);
            if (t == 0)
                emitlabel(label);
        }
    }

    class And extends Logical {
        public And(Token op, Expr expr1, Expr expr2) {
            super(op, expr1, expr2);
        }

        @Override
        public void jumping(int t, int f) {
            int label = f != 0 ? f : newlabel();
            expr1.jumping(0, label);
            expr2.jumping(t, f);
            if (f == 0)
                emitlabel(label);
        }
    }

    class Not extends Logical {
        public Not(Token op, Expr expr2) {
            super(op, expr2, expr2);
        }

        @Override
        public void jumping(int t, int f) {
            expr2.jumping(f, t);
        }

        @Override
        public String toString() {
            return op.toString() + " " + expr2.toString();
        }
    }

    // Relational operator.
    class Rel extends Logical {
        public Rel(Token op, Expr expr1, Expr expr2) {
            super(op, expr1, expr2);
        }

        public Type check(Type type1, Type type2) {
            if (type1 instanceof Array || type2 instanceof Array)
                return null;
            else if (type1 == type2)
                return Type.Bool;
            else
                return null;
        }

        @Override
        public void jumping(int t, int f) {
            Expr a = expr1.reduce();
            Expr b = expr2.reduce();
            String test = a.toString() + " " + op.toString() + " " + b.toString();
            emitjumps(test, t, f);
        }
    }

    // Array access.
    class Access extends Op {
        public Id array;
        public Expr index;

        public Access(Id array, Expr index, Type type) {
            super(new Word(Tag.INDEX, "[]"), type);
            this.array = array;
            this.index = index;
        }

        @Override
        public Expr gen() {
            return new Access(array, index.reduce(), type);
        }

        @Override
        public void jumping(int t, int f) {
            emitjumps(reduce().toString(), t, f);
        }

        @Override
        public String toString() {
            return array.toString() + " [ " + index.toString() + " ]";
        }
    }

    // ---------------------------------------------------------------------------
    // Statements
    // ---------------------------------------------------------------------------

    // Statement.
    class Stmt extends Node {
        public static final Stmt Null = new Stmt();
        public int after = 0; // save label after
        public static Stmt Enclosing = Stmt.Null; // used for break statement

        public Stmt() {
        }

        // called with labelds beging and after
        public void gen(int begin, int after) {
        }
    }

    // If statement.
    class If extends Stmt {
        public Expr expr;
        public Stmt stmt;

        public If(Expr expr, Stmt stmt) {
            this.expr = expr;
            this.stmt = stmt;
            if (expr.type != Type.Bool)
                expr.error("boolean required in if");
        }

        @Override
        public void gen(int begin, int after) {
            int label = newlabel();
            expr.jumping(0, after); // fall through on true, goto after on false
            emitlabel(label);
            stmt.gen(label, after);
        }
    }

    // If-Else statement.
    class Else extends Stmt {
        public Expr expr;
        public Stmt stmt1, stmt2;

        public Else(Expr expr, Stmt stmt1, Stmt stmt2) {
            this.expr = expr;
            this.stmt1 = stmt1;
            this.stmt2 = stmt2;
            if (expr.type != Type.Bool)
                expr.error("boolean required in if");
        }

        @Override
        public void gen(int begin, int after) {
            int label1 = newlabel(); // label1 for stmt1
            int label2 = newlabel(); // label2 fro stmt2
            expr.jumping(0, label2); // fall through to stmt1 on true
            emitlabel(label1);
            stmt1.gen(label1, after);
            emit("goto L" + after);
            emitlabel(label2);
            stmt2.gen(label2, after);
        }
    }

    // While statement.
    class While extends Stmt {
        public Expr expr;
        public Stmt stmt;

        public While() {
            expr = null;
            stmt = null;
        }

        public void init(Expr expr, Stmt stmt) {
            this.expr = expr;
            this.stmt = stmt;
            if (expr.type != Type.Bool)
                expr.error("boolean required in while");
        }

        @Override
        public void gen(int begin, int after) {
            this.after = after;
            expr.jumping(0, after);
            int label = newlabel(); // label for stmt
            emitlabel(label);
            stmt.gen(label, begin);
            emit("goto L" + begin);
        }
    }

    // Do-While statment.
    class Do extends Stmt {
        public Expr expr;
        public Stmt stmt;

        public Do() {
            expr = null;
            stmt = null;
        }

        public void init(Expr expr, Stmt stmt) {
            this.expr = expr;
            this.stmt = stmt;
            if (expr.type != Type.Bool)
                expr.error("boolean required in do");
        }

        @Override
        public void gen(int begin, int after) {
            this.after = after;
            int label = newlabel(); // label for expr
            stmt.gen(begin, label);
            emitlabel(label);
            expr.jumping(begin, 0);
        }
    }

    // Assignment with an identifier on LHS and an expression on RHS.
    class Set extends Stmt {
        public Id id;
        public Expr expr;

        public Set(Id id, Expr expr) {
            this.id = id;
            this.expr = expr;
            if (check(id.type, expr.type) == null)
                error("type error");
        }

        public Type check(Type type1, Type type2) {
            if (Type.numeric(type1) && Type.numeric(type2))
                return type2;
            else if (type1 == Type.Bool && type2 == Type.Bool)
                return type2;
            else
                return null;
        }

        @Override
        public void gen(int begin, int after) {
            emit(id.toString() + " = " + expr.gen().toString());
        }
    }

    // Assignment to an array element.
    class SetElem extends Stmt {
        public Id array;
        public Expr index, expr;

        public SetElem(Access access, Expr expr) {
            this.array = access.array;
            this.index = access.index;
            this.expr = expr;
            if (check(access.type, expr.type) == null)
                error("type error");
        }

        public Type check(Type type1, Type type2) {
            if (type1 instanceof Array || type2 instanceof Array)
                return null;
            else if (type1 == type2)
                return type2;
            else if (Type.numeric(type1) && Type.numeric(type2))
                return type2;
            else
                return null;
        }

        @Override
        public void gen(int begin, int after) {
            String s1 = index.reduce().toString();
            String s2 = expr.reduce().toString();
            emit(array.toString() + " [ " + s1 + " ] = " + s2);
        }
    }

    // A sequence of statements.
    class Seq extends Stmt {
        public Stmt stmt1, stmt2;

        public Seq(Stmt stmt1, Stmt stmt2) {
            this.stmt1 = stmt1;
            this.stmt2 = stmt2;
        }

        @Override
        public void gen(int begin, int after) {
            if (stmt1 == Stmt.Null)
                stmt2.gen(begin, after);
            else if (stmt2 == Stmt.Null)
                stmt1.gen(begin, after);
            else {
                int label = newlabel();
                stmt1.gen(begin, label);
                emitlabel(label);
                stmt2.gen(label, after);
            }
        }
    }

    // Break statement.
    class Break extends Stmt {
        public Stmt stmt;

        public Break() {
            if (Stmt.Enclosing == Stmt.Null)
                error("unenclosed brean");
            stmt = Stmt.Enclosing;
        }

        @Override
        public void gen(int begin, int after) {
            emit("goto L" + stmt.after);
        }
    }
}
