package com.spike.compiler.dragon.example.frontend;

import java.io.IOException;

import com.spike.compiler.dragon.example.frontend.inter.Access;
import com.spike.compiler.dragon.example.frontend.inter.And;
import com.spike.compiler.dragon.example.frontend.inter.Arith;
import com.spike.compiler.dragon.example.frontend.inter.Break;
import com.spike.compiler.dragon.example.frontend.inter.Constant;
import com.spike.compiler.dragon.example.frontend.inter.Do;
import com.spike.compiler.dragon.example.frontend.inter.Else;
import com.spike.compiler.dragon.example.frontend.inter.Expr;
import com.spike.compiler.dragon.example.frontend.inter.Id;
import com.spike.compiler.dragon.example.frontend.inter.If;
import com.spike.compiler.dragon.example.frontend.inter.Not;
import com.spike.compiler.dragon.example.frontend.inter.Or;
import com.spike.compiler.dragon.example.frontend.inter.Rel;
import com.spike.compiler.dragon.example.frontend.inter.Seq;
import com.spike.compiler.dragon.example.frontend.inter.Set;
import com.spike.compiler.dragon.example.frontend.inter.SetElem;
import com.spike.compiler.dragon.example.frontend.inter.Stmt;
import com.spike.compiler.dragon.example.frontend.inter.Unary;
import com.spike.compiler.dragon.example.frontend.inter.While;
import com.spike.compiler.dragon.example.frontend.lexer.Lexer;
import com.spike.compiler.dragon.example.frontend.lexer.Tag;
import com.spike.compiler.dragon.example.frontend.lexer.Token;
import com.spike.compiler.dragon.example.frontend.lexer.Word;
import com.spike.compiler.dragon.example.frontend.lexer.Num;
import com.spike.compiler.dragon.example.frontend.symbols.Env;
import com.spike.compiler.dragon.example.frontend.symbols.Type;
import com.spike.compiler.dragon.example.frontend.symbols.Array;

interface parser {
    class Parser {
        private final Lexer lexer; // lexical analyzer for this parser
        private Token look; // lookahead token
        Env top = null;// current or top symbol table
        int used = 0; // storage used for declarations

        public Parser(Lexer lexer) throws IOException {
            this.lexer = lexer;
            move();
        }

        void move() throws IOException {
            look = lexer.scan();
            System.out.println("DEBUG: move in line: " + lexer.line() + " token: " + look.toString());
        }

        void error(String s) {
            throw new Error("near line " + lexer.line() + ": " + s);
        }

        void match(int tag) throws IOException {
            if (look.tag == tag)
                move();
            else
                error("syntax error");
        }

        // program -> block
        public void program() throws IOException {
            Stmt stmt = block();
            int begin = stmt.newlabel();
            int after = stmt.newlabel();
            stmt.emitlabel(begin);
            stmt.gen(begin, after);
            stmt.emitlabel(after);
        }

        // block -> { decls stmts }
        Stmt block() throws IOException {
            match('{');
            Env savedEnv = top;
            top = new Env(top);
            decls();
            Stmt stmt = stmts();
            match('}');
            top = savedEnv;
            return stmt;
        }

        // decls -> decls decl | ε
        void decls() throws IOException {
            // decl -> type `id` ;
            while (look.tag == Tag.BASIC) {
                Type type = type();
                Token token = look;
                match(Tag.ID);
                match(';');
                Id id = new Id((Word) token, type, used);
                top.put(token, id);
                used = used + type.width;
            }
        }

        // type -> type [ `num` ] | `basic`
        Type type() throws IOException {
            Type type = (Type) look; // look.tag == Tag.BASIC
            match(Tag.BASIC);
            if (look.tag != '[') // basic type
                return type;
            else // array type
                return dims(type);
        }

        Type dims(Type type) throws IOException {
            match('[');
            Token token = look;
            match(Tag.NUM);
            match(']');
            if (look.tag == '[')
                type = dims(type);
            return new Array(((Num) token).value, type);
        }

        // stmts -> stmts stmt | ε
        Stmt stmts() throws IOException {
            if (look.tag == '}')
                return Stmt.Null;
            else
                return new Seq(stmt(), stmts());
        }

        // stmt -> loc = bool ;
        // | 'if' ( bool ) stmt
        // | 'if' ( bool ) stmt 'else' stmt
        // | 'while' ( bool ) stmt
        // | 'do' stmt 'while' ( bool ) ;
        // | 'break' ;
        // | block
        //
        // loc->loc [ bool ] | `id`
        Stmt stmt() throws IOException {
            Expr expr;
            Stmt stmt1, stmt2;
            Stmt savedStmt;
            switch (look.tag) {
                case ';':
                    move();
                    return Stmt.Null;
                case Tag.IF:
                    match(Tag.IF);
                    match('(');
                    expr = bool();
                    match(')');
                    stmt1 = stmt();
                    if (look.tag != Tag.ELSE)
                        return new If(expr, stmt1);
                    match(Tag.ELSE);
                    stmt2 = stmt();
                    return new Else(expr, stmt1, stmt2);
                case Tag.WHILE:
                    While whileNode = new While();
                    savedStmt = Stmt.Enclosing;
                    Stmt.Enclosing = whileNode;
                    match(Tag.WHILE);
                    match('(');
                    expr = bool();
                    match(')');
                    stmt1 = stmt();
                    whileNode.init(expr, stmt1);
                    Stmt.Enclosing = savedStmt;
                    return whileNode;
                case Tag.DO:
                    Do doNode = new Do();
                    savedStmt = Stmt.Enclosing;
                    Stmt.Enclosing = doNode;
                    match(Tag.DO);
                    stmt1 = stmt();
                    match(Tag.WHILE);
                    match('(');
                    expr = bool();
                    match(')');
                    match(';');
                    doNode.init(expr, stmt1);
                    Stmt.Enclosing = savedStmt;
                    return doNode;
                case Tag.BREAK:
                    match(Tag.BREAK);
                    match(';');
                    return new Break();
                case '{':
                    return block();
                default:
                    return assign();
            }
        }

        Stmt assign() throws IOException {
            Stmt stmt;
            Token token = look;
            match(Tag.ID);
            Id id = top.get(token);
            if (id == null)
                error(token.toString() + " undeclared");
            if (look.tag == '=') { // id = bool
                move();
                stmt = new Set(id, bool());
            } else { // loc [ bool ] = bool
                Access access = offset(id);
                match('=');
                stmt = new SetElem(access, bool());
            }
            match(';');
            return stmt;
        }

        // loc -> loc [ bool ] | `id`
        Access offset(Id id) throws IOException {
            Expr i, w, t1, t2, loc;
            Type type = id.type;
            match(('['));
            i = bool();
            match(']'); // first index: I -> [ E ]
            type = ((Array) type).of;
            w = new Constant(type.width);
            t1 = new Arith(new Token('*'), i, w);
            loc = t1;
            while (look.tag == '[') { // multi-dim: I -> [ E ] I
                match('[');
                i = bool();
                match(']');
                type = ((Array) type).of;
                w = new Constant(type.width);
                t1 = new Arith(new Token('*'), i, w);
                t2 = new Arith(new Token('+'), loc, t1);
                loc = t2;
            }
            return new Access(id, loc, type);
        }

        // bool -> bool || join | join
        Expr bool() throws IOException {
            Expr expr = join();
            while (look.tag == Tag.OR) {
                Token token = look;
                move();
                expr = new Or(token, expr, join());
            }
            return expr;
        }

        // join -> join && equality | equality
        Expr join() throws IOException {
            Expr expr = equality();
            while (look.tag == Tag.AND) {
                Token token = look;
                move();
                expr = new And(token, expr, equality());
            }
            return expr;
        }

        // equality -> equality == rel | equality != rel | rel
        Expr equality() throws IOException {
            Expr expr = rel();
            while (look.tag == Tag.EQ || look.tag == Tag.NE) {
                Token token = look;
                move();
                expr = new Rel(token, expr, rel());
            }
            return expr;
        }

        // rel -> expr < expr | expr <= expr | expre >= expr | expr > expr | expr
        Expr rel() throws IOException {
            Expr expr = expr();
            switch (look.tag) {
                case '<':
                case Tag.LE:
                case Tag.GE:
                case '>':
                    Token token = look;
                    move();
                    return new Rel(token, expr, expr());
                default:
                    return expr;
            }
        }

        // expr -> expr + term | expr - term | term
        Expr expr() throws IOException {
            Expr expr = term();
            while (look.tag == '+' || look.tag == '-') {
                Token token = look;
                move();
                expr = new Arith(token, expr, term());
            }
            return expr;
        }

        // term -> term * unary | term / unary | unary
        Expr term() throws IOException {
            Expr expr = unary();
            while (look.tag == '*' || look.tag == '/') {
                Token token = look;
                move();
                expr = new Arith(token, expr, unary());
            }
            return expr;
        }

        // unary -> ! unary | - unary | factor
        Expr unary() throws IOException {
            if (look.tag == '-') {
                move();
                return new Unary(Word.minus, unary());
            } else if (look.tag == '!') {
                Token token = look;
                move();
                return new Not(token, unary());
            } else
                return factor();
        }

        // factor -> ( bool ) | loc | `num` | `real` | 'true' | 'false'
        Expr factor() throws IOException {
            Expr expr = null;
            switch (look.tag) {
                case '(':
                    move();
                    expr = bool();
                    match(')');
                    return expr;
                case Tag.NUM:
                    expr = new Constant(look, Type.Int);
                    move();
                    return expr;
                case Tag.REAL:
                    expr = new Constant(look, Type.Float);
                    move();
                    return expr;
                case Tag.TRUE:
                    expr = Constant.True;
                    move();
                    return expr;
                case Tag.FALSE:
                    expr = Constant.False;
                    move();
                    return expr;
                case Tag.ID:
                    String s = look.toString();
                    Id id = top.get(look);
                    if (id == null)
                        error(s + " undeclared");
                    move();
                    if (look.tag != '[')
                        return id;
                    else
                        return offset(id);
                default:
                    error("syntax error");
                    return expr;
            }
        }
    }
}
