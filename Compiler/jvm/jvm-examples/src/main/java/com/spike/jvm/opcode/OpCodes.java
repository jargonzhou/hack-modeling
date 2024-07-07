package com.spike.jvm.opcode;

import static com.spike.jvm.opcode.OpcodeCategory.Math;
import static com.spike.jvm.opcode.OpcodeCategory.*;

/**
 * @see org.objectweb.asm.Opcodes
 */
public class OpCodes {
    public static final Opcode nop = new Opcode(0, "nop", Constants, "Do nothing");
    public static final Opcode aconst_null = new Opcode(1, "aconst_null", Constants, "Push null");
    public static final Opcode iconst_m1 = new Opcode(2, "iconst_m1", Constants, "Push int constant");
    public static final Opcode iconst_0 = new Opcode(3, "iconst_0", Constants, "Push int constant");
    public static final Opcode iconst_1 = new Opcode(4, "iconst_1", Constants, "Push int constant");
    public static final Opcode iconst_2 = new Opcode(5, "iconst_2", Constants, "Push int constant");
    public static final Opcode iconst_3 = new Opcode(6, "iconst_3", Constants, "Push int constant");
    public static final Opcode iconst_4 = new Opcode(7, "iconst_4", Constants, "Push int constant");
    public static final Opcode iconst_5 = new Opcode(8, "iconst_5", Constants, "Push int constant");
    public static final Opcode lconst_0 = new Opcode(9, "lconst_0", Constants, "Push long constant");
    public static final Opcode lconst_1 = new Opcode(10, "lconst_1", Constants, "Push long constant");
    public static final Opcode fconst_0 = new Opcode(11, "fconst_0", Constants, "Push float");
    public static final Opcode fconst_1 = new Opcode(12, "fconst_1", Constants, "Push float");
    public static final Opcode fconst_2 = new Opcode(13, "fconst_2", Constants, "Push float");
    public static final Opcode dconst_0 = new Opcode(14, "dconst_0", Constants, "Push double");
    public static final Opcode dconst_1 = new Opcode(15, "dconst_1", Constants, "Push double");
    public static final Opcode bipush = new Opcode(16, "bipush", Constants, "Push byte");
    public static final Opcode sipush = new Opcode(17, "sipush", Constants, "Push short");
    public static final Opcode ldc = new Opcode(18, "ldc", Constants, "Push item from run-time constant pool");
    public static final Opcode ldc_w = new Opcode(19, "ldc_w", Constants, "Push item from run-time constant pool (wide index)");
    public static final Opcode ldc2_w = new Opcode(20, "ldc2_w", Constants, "Push long or double from run-time constant pool (wide index)");

    public static final Opcode iload = new Opcode(21, "iload", Loads, "Load int from local variable");
    public static final Opcode lload = new Opcode(22, "lload", Loads, "Load long from local variable");
    public static final Opcode fload = new Opcode(23, "fload", Loads, "Load float from local variable");
    public static final Opcode dload = new Opcode(24, "dload", Loads, "Load double from local variable");
    public static final Opcode aload = new Opcode(25, "aload", Loads, "Load reference from local variable");
    public static final Opcode iload_0 = new Opcode(26, "iload_0", Loads, "Load int from local variable");
    public static final Opcode iload_1 = new Opcode(27, "iload_1", Loads, "Load int from local variable");
    public static final Opcode iload_2 = new Opcode(28, "iload_2", Loads, "Load int from local variable");
    public static final Opcode iload_3 = new Opcode(29, "iload_3", Loads, "Load int from local variable");
    public static final Opcode lload_0 = new Opcode(30, "lload_0", Loads, "Load long from local variable");
    public static final Opcode lload_1 = new Opcode(31, "lload_1", Loads, "Load long from local variable");
    public static final Opcode lload_2 = new Opcode(32, "lload_2", Loads, "Load long from local variable");
    public static final Opcode lload_3 = new Opcode(33, "lload_3", Loads, "Load long from local variable");
    public static final Opcode fload_0 = new Opcode(34, "fload_0", Loads, "Load float from local variable");
    public static final Opcode fload_1 = new Opcode(35, "fload_1", Loads, "Load float from local variable");
    public static final Opcode fload_2 = new Opcode(36, "fload_2", Loads, "Load float from local variable");
    public static final Opcode fload_3 = new Opcode(37, "fload_3", Loads, "Load float from local variable");
    public static final Opcode dload_0 = new Opcode(38, "dload_0", Loads, "Load double from local variable");
    public static final Opcode dload_1 = new Opcode(39, "dload_1", Loads, "Load double from local variable");
    public static final Opcode dload_2 = new Opcode(40, "dload_2", Loads, "Load double from local variable");
    public static final Opcode dload_3 = new Opcode(41, "dload_3", Loads, "Load double from local variable");
    public static final Opcode aload_0 = new Opcode(42, "aload_0", Loads, "Load reference from local variable");
    public static final Opcode aload_1 = new Opcode(43, "aload_1", Loads, "Load reference from local variable");
    public static final Opcode aload_2 = new Opcode(44, "aload_2", Loads, "Load reference from local variable");
    public static final Opcode aload_3 = new Opcode(45, "aload_3", Loads, "Load reference from local variable");
    public static final Opcode iaload = new Opcode(46, "iaload", Loads, "Load int from array");
    public static final Opcode laload = new Opcode(47, "laload", Loads, "Load long from array");
    public static final Opcode faload = new Opcode(48, "faload", Loads, "Load float from array");
    public static final Opcode daload = new Opcode(49, "daload", Loads, "Load double from array");
    public static final Opcode aaload = new Opcode(50, "aaload", Loads, "Load reference from array");
    public static final Opcode baload = new Opcode(51, "baload", Loads, "Load byte or boolean from array");
    public static final Opcode caload = new Opcode(52, "caload", Loads, "Load char from array");
    public static final Opcode saload = new Opcode(53, "saload", Loads, "Load short from array");

    public static final Opcode istore = new Opcode(54, "istore", Stores, "Store int into local variable");
    public static final Opcode lstore = new Opcode(55, "lstore", Stores, "Store long into local variable");
    public static final Opcode fstore = new Opcode(56, "fstore", Stores, "Store float into local variable");
    public static final Opcode dstore = new Opcode(57, "dstore", Stores, "Store double into local variable");
    public static final Opcode astore = new Opcode(58, "astore", Stores, "Store reference into local variable");
    public static final Opcode istore_0 = new Opcode(59, "istore_0", Stores, "Store int into local variable");
    public static final Opcode istore_1 = new Opcode(60, "istore_1", Stores, "Store int into local variable");
    public static final Opcode istore_2 = new Opcode(61, "istore_2", Stores, "Store int into local variable");
    public static final Opcode istore_3 = new Opcode(62, "istore_3", Stores, "Store int into local variable");
    public static final Opcode lstore_0 = new Opcode(63, "lstore_0", Stores, "Store long into local variable");
    public static final Opcode lstore_1 = new Opcode(64, "lstore_1", Stores, "Store long into local variable");
    public static final Opcode lstore_2 = new Opcode(65, "lstore_2", Stores, "Store long into local variable");
    public static final Opcode lstore_3 = new Opcode(66, "lstore_3", Stores, "Store long into local variable");
    public static final Opcode fstore_0 = new Opcode(67, "fstore_0", Stores, "Store float into local variable");
    public static final Opcode fstore_1 = new Opcode(68, "fstore_1", Stores, "Store float into local variable");
    public static final Opcode fstore_2 = new Opcode(69, "fstore_2", Stores, "Store float into local variable");
    public static final Opcode fstore_3 = new Opcode(70, "fstore_3", Stores, "Store float into local variable");
    public static final Opcode dstore_0 = new Opcode(71, "dstore_0", Stores, "Store double into local variable");
    public static final Opcode dstore_1 = new Opcode(72, "dstore_1", Stores, "Store double into local variable");
    public static final Opcode dstore_2 = new Opcode(73, "dstore_2", Stores, "Store double into local variable");
    public static final Opcode dstore_3 = new Opcode(74, "dstore_3", Stores, "Store double into local variable");
    public static final Opcode astore_0 = new Opcode(75, "astore_0", Stores, "Store reference into local variable");
    public static final Opcode astore_1 = new Opcode(76, "astore_1", Stores, "Store reference into local variable");
    public static final Opcode astore_2 = new Opcode(77, "astore_2", Stores, "Store reference into local variable");
    public static final Opcode astore_3 = new Opcode(78, "astore_3", Stores, "Store reference into local variable");
    public static final Opcode iastore = new Opcode(79, "iastore", Stores, "Store into int array");
    public static final Opcode lastore = new Opcode(80, "lastore", Stores, "Store into long array");
    public static final Opcode fastore = new Opcode(81, "fastore", Stores, "Store into float array");
    public static final Opcode dastore = new Opcode(82, "dastore", Stores, "Store into double array");
    public static final Opcode aastore = new Opcode(83, "aastore", Stores, "Store into reference array");
    public static final Opcode bastore = new Opcode(84, "bastore", Stores, "Store into byte or boolean array");
    public static final Opcode castore = new Opcode(85, "castore", Stores, "Store into char array");
    public static final Opcode sastore = new Opcode(86, "sastore", Stores, "Store into short array");

    public static final Opcode pop = new Opcode(87, "pop", Stack, "Pop the top operand stack value");
    public static final Opcode pop2 = new Opcode(88, "pop2", Stack, "Pop the top one or two operand stack values");
    public static final Opcode dup = new Opcode(89, "dup", Stack, "Duplicate the top operand stack value");
    public static final Opcode dup_x1 = new Opcode(90, "dup_x1", Stack, "Duplicate the top operand stack value and insert two values down");
    public static final Opcode dup_x2 = new Opcode(91, "dup_x2", Stack, "Duplicate the top operand stack value and insert two or three values down");
    public static final Opcode dup2 = new Opcode(92, "dup2", Stack, "Duplicate the top one or two operand stack values");
    public static final Opcode dup2_x1 = new Opcode(93, "dup2_x1", Stack, "Duplicate the top one or two operand stack values and insert two or three values down");
    public static final Opcode dup2_x2 = new Opcode(94, "dup2_x2", Stack, "Duplicate the top one or two operand stack values and insert two, three, or four values down");
    public static final Opcode swap = new Opcode(95, "swap", Stack, "Swap the top two operand stack values");

    public static final Opcode iadd = new Opcode(96, "iadd", Math, "Add int");
    public static final Opcode ladd = new Opcode(97, "ladd", Math, "Add long");
    public static final Opcode fadd = new Opcode(98, "fadd", Math, "Add float");
    public static final Opcode dadd = new Opcode(99, "dadd", Math, "Add double");
    public static final Opcode isub = new Opcode(100, "isub", Math, "Subtract int");
    public static final Opcode lsub = new Opcode(101, "lsub", Math, "Subtract long");
    public static final Opcode fsub = new Opcode(102, "fsub", Math, "Subtract float");
    public static final Opcode dsub = new Opcode(103, "dsub", Math, "Subtract double");
    public static final Opcode imul = new Opcode(104, "imul", Math, "Multiply int");
    public static final Opcode lmul = new Opcode(105, "lmul", Math, "Multiply long");
    public static final Opcode fmul = new Opcode(106, "fmul", Math, "Multiply float");
    public static final Opcode dmul = new Opcode(107, "dmul", Math, "Multiply double");
    public static final Opcode idiv = new Opcode(108, "idiv", Math, "Divide int");
    public static final Opcode ldiv = new Opcode(109, "ldiv", Math, "Divide long");
    public static final Opcode fdiv = new Opcode(110, "fdiv", Math, "Divide float");
    public static final Opcode ddiv = new Opcode(111, "ddiv", Math, "Divide double");
    public static final Opcode irem = new Opcode(112, "irem", Math, "Remainder int");
    public static final Opcode lrem = new Opcode(113, "lrem", Math, "Remainder long");
    public static final Opcode frem = new Opcode(114, "frem", Math, "Remainder float");
    public static final Opcode drem = new Opcode(115, "drem", Math, "Remainder double");
    public static final Opcode ineg = new Opcode(116, "ineg", Math, "Negate int");
    public static final Opcode lneg = new Opcode(117, "lneg", Math, "Negate long");
    public static final Opcode fneg = new Opcode(118, "fneg", Math, "Negate float");
    public static final Opcode dneg = new Opcode(119, "dneg", Math, "Negate double");
    public static final Opcode ishl = new Opcode(120, "ishl", Math, "Shift left int");
    public static final Opcode lshl = new Opcode(121, "lshl", Math, "Shift left long");
    public static final Opcode ishr = new Opcode(122, "ishr", Math, "Arithmetic shift right int");
    public static final Opcode lshr = new Opcode(123, "lshr", Math, "Arithmetic shift right long");
    public static final Opcode iushr = new Opcode(124, "iushr", Math, "Logical shift right int");
    public static final Opcode lushr = new Opcode(125, "lushr", Math, "Logical shift right long");
    public static final Opcode iand = new Opcode(126, "iand", Math, "Boolean AND int");
    public static final Opcode land = new Opcode(127, "land", Math, "Boolean AND long");
    public static final Opcode ior = new Opcode(128, "ior", Math, "Boolean OR int");
    public static final Opcode lor = new Opcode(129, "lor", Math, "Boolean OR long");
    public static final Opcode ixor = new Opcode(130, "ixor", Math, "Boolean XOR int");
    public static final Opcode lxor = new Opcode(131, "lxor", Math, "Boolean XOR long");
    public static final Opcode iinc = new Opcode(132, "iinc", Math, "Increment local variable by constant");

    public static final Opcode i2l = new Opcode(133, "i2l", Conversions, "Convert int to long");
    public static final Opcode i2f = new Opcode(134, "i2f", Conversions, "Convert int to float");
    public static final Opcode i2d = new Opcode(135, "i2d", Conversions, "Convert int to double");
    public static final Opcode l2i = new Opcode(136, "l2i", Conversions, "Convert long to int");
    public static final Opcode l2f = new Opcode(137, "l2f", Conversions, "Convert long to float");
    public static final Opcode l2d = new Opcode(138, "l2d", Conversions, "Convert long to double");
    public static final Opcode f2i = new Opcode(139, "f2i", Conversions, "Convert float to int");
    public static final Opcode f2l = new Opcode(140, "f2l", Conversions, "Convert float to long");
    public static final Opcode f2d = new Opcode(141, "f2d", Conversions, "Convert float to double");
    public static final Opcode d2i = new Opcode(142, "d2i", Conversions, "Convert double to int");
    public static final Opcode d2l = new Opcode(143, "d2l", Conversions, "Convert double to long");
    public static final Opcode d2f = new Opcode(144, "d2f", Conversions, "Convert double to float");
    public static final Opcode i2b = new Opcode(145, "i2b", Conversions, "Convert int to byte");
    public static final Opcode i2c = new Opcode(146, "i2c", Conversions, "Convert int to char");
    public static final Opcode i2s = new Opcode(147, "i2s", Conversions, "Convert int to short");

    public static final Opcode lcmp = new Opcode(148, "lcmp", Comparisons, "Compare long");
    public static final Opcode fcmpl = new Opcode(149, "fcmpl", Comparisons, "Compare float");
    public static final Opcode fcmpg = new Opcode(150, "fcmpg", Comparisons, "Compare float");
    public static final Opcode dcmpl = new Opcode(151, "dcmpl", Comparisons, "Compare double");
    public static final Opcode dcmpg = new Opcode(152, "dcmpg", Comparisons, "Compare double");
    public static final Opcode ifeq = new Opcode(153, "ifeq", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode ifne = new Opcode(154, "ifne", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode iflt = new Opcode(155, "iflt", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode ifge = new Opcode(156, "ifge", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode ifgt = new Opcode(157, "ifgt", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode ifle = new Opcode(158, "ifle", Comparisons, "Branch if int comparison with zero succeeds");
    public static final Opcode if_icmpeq = new Opcode(159, "if_icmpeq", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_icmpne = new Opcode(160, "if_icmpne", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_icmplt = new Opcode(161, "if_icmplt", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_icmpge = new Opcode(162, "if_icmpge", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_icmpgt = new Opcode(163, "if_icmpgt", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_icmple = new Opcode(164, "if_icmple", Comparisons, "Branch if int comparison succeeds");
    public static final Opcode if_acmpeq = new Opcode(165, "if_acmpeq", Comparisons, "Branch if reference comparison succee");
    public static final Opcode if_acmpne = new Opcode(166, "if_acmpne", Comparisons, "Branch if reference comparison succee");

    public static final Opcode goto_ = new Opcode(167, "goto", Control, "Branch always");
    public static final Opcode jsr = new Opcode(168, "jsr", Control, "Jump subroutine");
    public static final Opcode ret = new Opcode(169, "ret", Control, "Return from subroutine");
    public static final Opcode tableswitch = new Opcode(170, "tableswitch", Control, "Access jump table by index and jump");
    public static final Opcode lookupswitch = new Opcode(171, "lookupswitch", Control, "Access jump table by key match and jump");
    public static final Opcode ireturn = new Opcode(172, "ireturn", Control, "Return int from method");
    public static final Opcode lreturn = new Opcode(173, "lreturn", Control, "Return long from method");
    public static final Opcode freturn = new Opcode(174, "freturn", Control, "Return float from method");
    public static final Opcode dreturn = new Opcode(175, "dreturn", Control, "Return double from method");
    public static final Opcode areturn = new Opcode(176, "areturn", Control, "Return reference from method");
    public static final Opcode return_ = new Opcode(177, "return", Control, "Return void from method");

    public static final Opcode getstatic = new Opcode(178, "getstatic", References, "Get static field from class");
    public static final Opcode putstatic = new Opcode(179, "putstatic", References, "Set static field in class");
    public static final Opcode getfield = new Opcode(180, "getfield", References, "Fetch field from object");
    public static final Opcode putfield = new Opcode(181, "putfield", References, "Set field in object");
    public static final Opcode invokevirtual = new Opcode(182, "invokevirtual", References, "Invoke instance method; dispatch based on class");
    public static final Opcode invokespecial = new Opcode(183, "invokespecial", References, "Invoke instance method; special handling for superclass, private, and instance initialization method invocations");
    public static final Opcode invokestatic = new Opcode(184, "invokestatic", References, "Invoke a class (static) method");
    public static final Opcode invokeinterface = new Opcode(185, "invokeinterface", References, "Invoke interface method");
    public static final Opcode invokedynamic = new Opcode(186, "invokedynamic", References, "Invoke dynamic method");
    public static final Opcode new_ = new Opcode(187, "new", References, "Create new object");
    public static final Opcode newarray = new Opcode(188, "newarray", References, "Create new array");
    public static final Opcode anewarray = new Opcode(189, "anewarray", References, "Create new array of reference");
    public static final Opcode arraylength = new Opcode(190, "arraylength", References, "Get length of array");
    public static final Opcode athrow = new Opcode(191, "athrow", References, "Throw exception or error");
    public static final Opcode checkcast = new Opcode(192, "checkcast", References, "Check whether object is of given type");
    public static final Opcode instanceof_ = new Opcode(193, "instanceof", References, "Determine if object is of given type");
    public static final Opcode monitorenter = new Opcode(194, "monitorenter", References, "Enter monitor for object");
    public static final Opcode monitorexit = new Opcode(195, "monitorexit", References, "Exit monitor for object");

    public static final Opcode wide = new Opcode(196, "wide", Extended, "Extend local variable index by additional bytes");
    public static final Opcode multianewarray = new Opcode(197, "multianewarray", Extended, "Create new multidimensional array");
    public static final Opcode ifnull = new Opcode(198, "ifnull", Extended, "Branch if reference is null");
    public static final Opcode ifnonnull = new Opcode(199, "ifnonnull", Extended, "Branch if reference not null");
    public static final Opcode goto_w = new Opcode(200, "goto_w", Extended, "Branch always (wide index)");
    public static final Opcode jsr_w = new Opcode(201, "jsr_w", Extended, "Jump subroutine (wide index)");

    public static final Opcode breakpoint = new Opcode(202, "breakpoint", Reserved, "intended to be used by debuggers to implement breakpoints");
    public static final Opcode impdep1 = new Opcode(254, "impdep1", Reserved, "intended to provide back doors to implementation-specific functionality implemented in software and hardware");
    public static final Opcode impdep2 = new Opcode(255, "impdep2", Reserved, "intended to provide traps to implementation-specific functionality implemented in software and hardware");
}
