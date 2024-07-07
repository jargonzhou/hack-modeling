package com.spike.jvm.asm;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.util.TraceClassVisitor;

import static org.objectweb.asm.Opcodes.*;


public class PublicizeMethodAdapter extends ClassVisitor {
    public PublicizeMethodAdapter(int api, ClassVisitor cv) {
        super(ASM4, cv);
        this.cv = cv;
    }

    @Override
    public MethodVisitor visitMethod(
            int access,
            String name,
            String desc,
            String signature,
            String[] exceptions) {
        if (name.equals("toUnsignedString0")) {
            return cv.visitMethod(
                    ACC_PUBLIC + ACC_STATIC,
                    name,
                    desc,
                    signature,
                    exceptions);
        }
        return cv.visitMethod(
                access, name, desc, signature, exceptions);
    }

    @Override
    public void visitEnd() {
        cv.visitEnd();

        if (cv instanceof TraceClassVisitor) {
            System.out.println(((TraceClassVisitor) cv).p.getText());

        }
    }
}