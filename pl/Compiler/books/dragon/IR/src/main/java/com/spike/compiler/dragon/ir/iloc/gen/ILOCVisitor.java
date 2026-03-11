// Generated from ILOC.g4 by ANTLR 4.10.1
package com.spike.compiler.dragon.ir.iloc.gen;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link ILOCParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface ILOCVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link ILOCParser#program}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProgram(ILOCParser.ProgramContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(ILOCParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by the {@code singleInstr}
	 * labeled alternative in {@link ILOCParser#instr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSingleInstr(ILOCParser.SingleInstrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code instrList}
	 * labeled alternative in {@link ILOCParser#instr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInstrList(ILOCParser.InstrListContext ctx);
	/**
	 * Visit a parse tree produced by the {@code comment}
	 * labeled alternative in {@link ILOCParser#op}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitComment(ILOCParser.CommentContext ctx);
	/**
	 * Visit a parse tree produced by the {@code realOp}
	 * labeled alternative in {@link ILOCParser#op}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRealOp(ILOCParser.RealOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#sources}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSources(ILOCParser.SourcesContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#targets}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTargets(ILOCParser.TargetsContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#label}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLabel(ILOCParser.LabelContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#operand}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOperand(ILOCParser.OperandContext ctx);
	/**
	 * Visit a parse tree produced by {@link ILOCParser#opCode}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOpCode(ILOCParser.OpCodeContext ctx);
}