package com.spike.javacc.jjtree;

import com.spike.javacc.jjtree.calculator.ASTOperand;
import com.spike.javacc.jjtree.calculator.CalculatorDefaultVisitor;

public class CalculatorSumVisitor extends CalculatorDefaultVisitor {
    public int sum = 0;

    @Override
    public Object visit(ASTOperand node, Object data) {
        // preorder traversal
        sum += Integer.parseInt(node.jjtGetValue().toString());
        return super.visit(node, data);
    }

}
