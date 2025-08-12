package com.spike.compiler.dragon.example.frontend;

import java.io.IOException;

import com.spike.compiler.dragon.example.frontend.lexer.Lexer;
import com.spike.compiler.dragon.example.frontend.parser.Parser;

/**
 * A simple compiler frontend.
 *
 * <p>Input: example-frontend-input.txt.</p>
 * <p>Output: example-frontend-output.txt.</p>
 */
public class Main {
    public static void main(String[] args) throws IOException {
        Lexer lexer = new Lexer();
        Parser parser = new Parser(lexer);
        parser.program();
        System.out.println();
    }
}