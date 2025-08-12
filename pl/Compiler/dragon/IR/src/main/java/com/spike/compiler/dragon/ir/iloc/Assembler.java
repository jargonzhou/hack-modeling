package com.spike.compiler.dragon.ir.iloc;

import com.spike.compiler.dragon.ir.iloc.gen.*;
import com.spike.compiler.dragon.ir.iloc.models.Instr;
import com.spike.compiler.dragon.ir.iloc.models.Label;
import com.spike.compiler.dragon.ir.iloc.models.Num;
import com.spike.compiler.dragon.ir.iloc.models.Op;
import com.spike.compiler.dragon.ir.iloc.models.OpCode;
import com.spike.compiler.dragon.ir.iloc.models.OpList;
import com.spike.compiler.dragon.ir.iloc.models.Operand;
import com.spike.compiler.dragon.ir.iloc.models.Program;
import com.spike.compiler.dragon.ir.iloc.models.Reg;
import com.spike.compiler.dragon.ir.iloc.models.Str;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

public class Assembler {
    public Assembler() {
    }

    public Program assemble(String file) throws IOException {
        BaseErrorListener errorListener = new ErrorListener();

        Path path = Paths.get(file);
        CharStream cs = CharStreams.fromPath(path);

        ILOCLexer lexer = new ILOCLexer(cs);
        lexer.removeErrorListeners();
        lexer.addErrorListener(errorListener);

        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ILOCParser parser = new ILOCParser(tokens);
        parser.removeErrorListeners();
        parser.addErrorListener(errorListener);

        ILOCParser.ProgramContext programContext = parser.program();
        ILOCVisitorImpl ilocVisitor = new ILOCVisitorImpl();
        Program result = ilocVisitor.visitProgram(programContext);
        result.check();
        return result;
    }

    private static class ILOCVisitorImpl implements ILOCVisitor<Object> {
        /**
         * The program to be built.
         */
        private Program program;

        /**
         * The error listener of this visitor.
         */
        private ErrorListener errors;

        public ILOCVisitorImpl() {
            this.program = new Program();
            this.errors = new ErrorListener();
        }

        @Override
        public Program visitProgram(ILOCParser.ProgramContext ctx) {
            for (ILOCParser.DeclContext declContext : ctx.decl()) {
                visitDecl(declContext);
            }

            for (ILOCParser.InstrContext instructionCtx : ctx.instr()) {
                if (instructionCtx instanceof ILOCParser.SingleInstrContext) {
                    Instr instr = this.visitSingleInstr(
                            (ILOCParser.SingleInstrContext) instructionCtx);
                    if (instr != null) {
                        program.addInstr(instr);
                    }
                } else if (instructionCtx instanceof ILOCParser.InstrListContext) {
                    Instr instr = this.visitInstrList((ILOCParser.InstrListContext) instructionCtx);
                    if (instr != null) {
                        program.addInstr(instr);
                    }
                }
            }
            return program;
        }

        @Override
        public Void visitDecl(ILOCParser.DeclContext ctx) {
            Num symbol = new Num(ctx.ID().getText());
            int value = Integer.parseInt(ctx.NUM().getText());
            program.setSymb(symbol, value);
            return null;
        }

        @Override
        public Instr visitSingleInstr(ILOCParser.SingleInstrContext ctx) {
            Op result = visitOp(ctx.op());
            if (ctx.label() != null) {
                result.setLabel(visitLabel(ctx.label()));
            }
            return result;
        }

        @Override
        public Instr visitInstrList(ILOCParser.InstrListContext ctx) {
            OpList result = new OpList();
            for (ILOCParser.OpContext opCtx : ctx.op()) {
                result.addOp(visitOp(opCtx));
            }
            if (ctx.label() != null) {
                result.setLabel(visitLabel(ctx.label()));
            }
            return result;
        }

        private Op visitOp(ILOCParser.OpContext ctx) {
            if (ctx instanceof ILOCParser.CommentContext) {
                return visitComment((ILOCParser.CommentContext) ctx);
            } else if (ctx instanceof ILOCParser.RealOpContext) {
                return this.visitRealOp((ILOCParser.RealOpContext) ctx);
            } else {
                return null;
            }
        }

        @Override
        public Op visitComment(ILOCParser.CommentContext ctx) {
            Op result = new Op(OpCode.comment);
            result.setComment(ctx.COMMENT().getText().substring(2).trim());
            return result;
        }

        @Override
        public Op visitRealOp(ILOCParser.RealOpContext ctx) {
            OpCode opCode = visitOpCode(ctx.opCode());

            List<Operand> operands = visitSources(ctx.sources());
            if (ctx.targets() != null) {
                operands.addAll(visitTargets(ctx.targets()));
            }
            if (opCode.getSigSize() != operands.size()) {
                throw new FormatException("opcode " + opCode.name() + " invalid operands: " + operands);
            }
            List<Operand> finalOperands = new ArrayList<>();
            for (int i = 0; i < opCode.getSigSize(); i++) {
                Operand operand = operands.get(i);
                Operand.Type sig = opCode.getSig().get(i);
                if (Operand.Type.REG.equals(sig)
                        && Operand.Type.LABEL.equals(operand.getType())) {
                    operand = new Reg(((Label) operand).getValue());
                }
                finalOperands.add(operand);
            }

            Op op = new Op(opCode, finalOperands);
            if (ctx.COMMENT() != null) {
                op.setComment(ctx.COMMENT().getText().substring(2).trim());
            }
            return op;
        }

        @Override
        public List<Operand> visitSources(ILOCParser.SourcesContext ctx) {
            List<Operand> result = new ArrayList<>();
            for (ILOCParser.OperandContext operandCtx : ctx.operand()) {
                result.add(visitOperand(operandCtx));
            }
            return result;
        }

        @Override
        public List<Operand> visitTargets(ILOCParser.TargetsContext ctx) {
            List<Operand> result = new ArrayList<>();
            for (ILOCParser.OperandContext operandCtx : ctx.operand()) {
                result.add(visitOperand(operandCtx));
            }
            return result;
        }

        @Override
        public Label visitLabel(ILOCParser.LabelContext ctx) {
            return new Label(ctx.getText());
        }

        @Override
        public Operand visitOperand(ILOCParser.OperandContext ctx) {
            if (ctx.STR() != null) {
                return new Str(ctx.STR().getText()
                        .replaceAll("\"", ""));
            } else if (ctx.NUM() != null) {
                return new Num(Integer.parseInt(ctx.NUM().getText()));
            } else if (ctx.SYMB() != null) {
                return new Num(ctx.SYMB().getText().substring(1)); // drop @
            } else if (ctx.LAB() != null) {
                return new Num(new Label(ctx.LAB().getText().substring(1))); // drop #
            } else { // ID for label or register
                return new Label(ctx.ID().getText());
            }
        }

        @Override
        public OpCode visitOpCode(ILOCParser.OpCodeContext ctx) {
            return OpCode.parse(ctx.getText());
        }

        @Override
        public Object visit(ParseTree parseTree) {
            return parseTree;
        }

        @Override
        public Object visitChildren(RuleNode ruleNode) {
            return ruleNode;
        }

        @Override
        public Object visitTerminal(TerminalNode terminalNode) {
            return terminalNode;
        }

        @Override
        public Object visitErrorNode(ErrorNode errorNode) {
            return errorNode;
        }
    }

    private static class ErrorListener extends BaseErrorListener {
        private final List<String> errors = new ArrayList<>();

        @Override
        public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
            this.errors.add(String.format("Line %d:%d - %s", line, charPositionInLine, msg));
        }

        public void addError(Token token, String msg, Object... args) {
            int line = token.getLine();
            int charPositionInLine = token.getCharPositionInLine();
            msg = String.format(msg, args);
            msg = String.format("Line %d:%d - %s", line, charPositionInLine, msg);
            this.errors.add(msg);
        }

        public boolean hasErrors() {
            return !this.errors.isEmpty();
        }

        public List<String> getErrors() {
            return this.errors;
        }

        @Override
        public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {
        }

        @Override
        public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {
        }

        @Override
        public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {
        }
    }
}
