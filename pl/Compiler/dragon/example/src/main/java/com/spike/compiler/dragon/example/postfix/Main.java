package com.spike.compiler.dragon.example.postfix;

import java.io.IOException;

public class Main {
    public static void main(String[] args) throws IOException {
        Parser parser = new Parser();
        parser.expr();
        System.out.println();
    }
}

// outputs
//
// correct
// 9-5+2
// 95-2+
//
// only single digit support
// 12-5+2
// 1