package com.spike.jvm.asm;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.util.TraceClassVisitor;

import java.io.IOException;
import java.io.PrintWriter;

/**
 * Extends {@link java.lang.Integer} to implement {@link java.lang.Cloneable}.
 *
 * @see java.lang.Integer
 * @see java.lang.Cloneable
 */
public class CustomClassWriter {

    static String className = "java.lang.Integer";
    static String cloneableInterface = "java/lang/Cloneable";
    ClassReader reader;
    ClassWriter writer;
    PrintWriter pw = new PrintWriter(System.out);
    TraceClassVisitor tracer; // introspect the modified class

    AddFieldAdapter addFieldAdapter;
    PublicizeMethodAdapter pubMethAdapter;

    public CustomClassWriter() throws IOException {
        reader = new ClassReader(className);
        writer = new ClassWriter(reader, 0);
        tracer = new TraceClassVisitor(writer, pw);
    }

    public byte[] addField() {
        addFieldAdapter = new AddFieldAdapter(
                "aNewBooleanField",
                "V", // org.objectweb.asm.Type.getTypeInternal
                org.objectweb.asm.Opcodes.ACC_PUBLIC,
                writer);
        reader.accept(addFieldAdapter, 0);
        return writer.toByteArray();
    }

    public byte[] publicizeMethod() {
        pubMethAdapter = new PublicizeMethodAdapter(-1, tracer);
        reader.accept(pubMethAdapter, 0);
        return writer.toByteArray();
    }
}