package com.spike.javacc.error.logo;

import org.junit.jupiter.api.Test;

import java.io.StringReader;

// Use option 'STATIC = false;'
public class TestLogo {
    @Test
    public void shouldPass() throws ParseException {
        StringReader sr = new StringReader("FORWARD 20\n" +
                "RIGHT 120\n" +
                "FORWARD 20\n");
        Logo p = new Logo(sr);
        p.Program();
    }

    @Test
    public void shouldInvalidInputAlsoPass() throws ParseException {
        StringReader sr = new StringReader("FORWARD 20\n" +
                "RIGHT RIGHT 120\n" +
                "FORWARD 20\n");
        Logo p = new Logo(sr);
        p.Program();
    }
}
