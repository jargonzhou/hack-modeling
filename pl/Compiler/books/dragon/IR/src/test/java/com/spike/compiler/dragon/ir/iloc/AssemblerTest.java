package com.spike.compiler.dragon.ir.iloc;

import com.google.gson.ExclusionStrategy;
import com.google.gson.FieldAttributes;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.spike.compiler.dragon.ir.iloc.models.Program;
import com.spike.compiler.dragon.ir.iloc.models.gson.Exclude;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class AssemblerTest {
    @Test
    public void testAssemble() throws IOException {
        Assembler assembler = new Assembler();
        Path dir = Paths.get("src/test/resources/iloc");
        for (File f : dir.toFile().listFiles()) {
            System.out.println(f.getPath());
            Program program = assembler.assemble(f.getPath());
            System.out.println(program.prettyPrint());
            System.out.println();

            ExclusionStrategy strategy = new ExclusionStrategy() {
                @Override
                public boolean shouldSkipClass(Class<?> clazz) {
                    return false;
                }

                @Override
                public boolean shouldSkipField(FieldAttributes field) {
                    return field.getAnnotation(Exclude.class) != null;
                }
            };
            Gson gson = new GsonBuilder()
                    .addSerializationExclusionStrategy(strategy)
                    .setPrettyPrinting()
                    .create();;
            System.out.println(gson.toJson(program));
            System.out.println();
        }
    }
}
