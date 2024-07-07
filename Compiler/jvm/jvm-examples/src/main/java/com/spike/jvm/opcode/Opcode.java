package com.spike.jvm.opcode;

import java.util.List;

public class Opcode {
    public short index;
    public String opcode;
    public String operation;
    public OpcodeCategory category;

    public List<Throwable> linkingExceptions;
    public List<Throwable> runtimeExceptions;

    public Opcode(int index, String opcode, OpcodeCategory category, String operation) {
        this.index = (short) index;
        this.opcode = opcode;
        this.category = category;
        this.operation = operation;
    }
}
