package com.spike.compiler.dragon.ir.iloc;

import com.spike.compiler.dragon.ir.iloc.models.Op;
import com.spike.compiler.dragon.ir.iloc.models.OpCode;
import com.spike.compiler.dragon.ir.iloc.models.Program;
import com.spike.compiler.dragon.ir.iloc.vm.Machine;
import org.junit.Assert;
import org.junit.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

public class SimulatorTest {
    private static final String DIR_PATH = "src/test/resources/iloc/";

    @Test
    public void testRunLoadStore() throws IOException {
        String path = DIR_PATH + "fig1-3-init.iloc";
        Program prog = new Assembler().assemble(path);

        prog.addInstr(new Op(OpCode.nop));
        Simulator.DEBUG = true;

        Machine machine = new Machine();

        // set up: a=1, b=2, c=3, d=4
        machine.store(1, 0);
        machine.store(2, 4);
        machine.store(3, 8);
        machine.store(4, 12);

        Simulator simulator = new Simulator(prog, machine);
        simulator.run();

        int result = machine.load(0);

        // (a * 2 * b * c) * d = (1 * 2 * 2 * 3) * 4 = 48
        Assert.assertEquals(48, result);
    }

    @Test
    public void testRunStack() throws IOException {
        String path = DIR_PATH + "fig1-3-stack.iloc";
        Program prog = new Assembler().assemble(path);

        prog.addInstr(new Op(OpCode.nop));
        Simulator.DEBUG = true;

        Machine machine = new Machine();

        // set up: a=1, b=2, c=3, d=4
        machine.store(1, 0);
        machine.store(2, 4);
        machine.store(3, 8);
        machine.store(4, 12);

        Simulator simulator = new Simulator(prog, machine);
        simulator.run();

        int result = machine.load(0);

        // (a * 2 * b) * (c * d) = (1 * 2 * 2) * (3 * 4) = 48
        Assert.assertEquals(48, result);
    }

    @Test
    public void testRunString() throws IOException {
        String path = DIR_PATH + "string.iloc";
        Program prog = new Assembler().assemble(path);

        prog.addInstr(new Op(OpCode.nop));
        Simulator.DEBUG = true;

        Machine machine = new Machine();

        Simulator simulator = new Simulator(prog, machine);
        ByteArrayInputStream in = new ByteArrayInputStream("abcd".getBytes());
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        simulator.setIn(in);
        simulator.setOut(out);

        simulator.run();

        Assert.assertEquals("Doubled: abcdabcd\n", out.toString());
    }

    @Test(expected = ArrayIndexOutOfBoundsException.class)
    public void testRunStringFailed() throws IOException {
        String path = DIR_PATH + "string4.iloc";
        Program prog = new Assembler().assemble(path);

        prog.addInstr(new Op(OpCode.nop));
        Simulator.DEBUG = true;

        Machine machine = new Machine();

        Simulator simulator = new Simulator(prog, machine);
        ByteArrayInputStream in = new ByteArrayInputStream("abcd".getBytes());
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        simulator.setIn(in);
        simulator.setOut(out);

        simulator.run();

        System.out.println(out.toString());
    }
}
