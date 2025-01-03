package com.spike.javacc;

import com.spike.javacc.simple.ParseException;
import com.spike.javacc.simple.SimpleParser;

public class SimpleMain {
    public static void main(String[] args) {
        try {
            SimpleParser.main(args);
        } catch (ParseException e) {
            throw new RuntimeException(e);
        }
    }
}
