package com.spike.javacc.examples.postfix_expr;

import java.util.Objects;
import java.util.Stack;

public class PostfixExprCalcVisitor extends PostfixExprDefaultVisitor {
    public Stack<Integer> stack = new Stack<>();

    @Override
    public Object visit(ASTFactor node, Object data) {
        stack.push(Integer.parseInt(node.jjtGetValue().toString()));
        System.out.println("Push " + node.jjtGetValue());
        return super.visit(node, data);
    }

    @Override
    public Object visit(ASTOperator node, Object data) {
        boolean isPlus = Objects.nonNull(node.jjtGetValue()) &&
                Boolean.parseBoolean(node.jjtGetValue().toString());
        System.out.println("Got operator " + (isPlus ? "+" : "-"));
        Integer op2 = stack.pop();
        Integer op1 = stack.pop();
        if (isPlus) {
            stack.push(op1 + op2);
        } else {
            stack.push(op1 - op2);
        }
        System.out.println("Stack top is " + stack.peek());
        return super.visit(node, data);
    }

}
