/**
 * A complete frond end.
 * <p>
 * program -> block
 * block -> { decls stmts }
 * decls -> decls decl | ε
 * decl -> type `id` ;
 * type -> type [ `num` ] | `basic` # basic represents basic types
 * stmts -> stmts stmt | ε
 * <p>
 * stmt -> loc = bool ;
 * | 'if' ( bool ) stmt
 * | 'if' ( bool ) stmt 'else' stmt
 * | 'while' ( bool ) stmt
 * | 'do' stmt 'while' ( bool ) ;
 * | 'break' ;
 * | block
 * loc -> loc [ bool ] | `id`
 * <p>
 * bool -> bool || join | join
 * join -> join && equality | equality
 * equality -> equality == rel | equality != rel | rel
 * rel -> expr < expr | expr <= expr | expre >= expr | expr > expr | expr
 * expr -> expr + term | expr - term | term
 * term -> term * unary | term / unary | unary
 * unary -> ! unary | - unary | factor
 * factor -> ( bool ) | loc | `num` | `real` | 'true' | 'false'
 */
package com.spike.compiler.dragon.example.frontend;