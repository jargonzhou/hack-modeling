package com.spike.jvm.asm;

import org.junit.Test;

import java.io.IOException;

// https://www.baeldung.com/java-asm
public class TestCustomClassWriter {
    @Test
    public void test() throws IOException {
        CustomClassWriter cw = new CustomClassWriter();

        cw.addField();
        cw.publicizeMethod();

        cw.writer.toByteArray();
    }
}
