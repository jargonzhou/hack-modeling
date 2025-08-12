grammar ILOC;

@header {package com.spike.compiler.dragon.ir.iloc.gen;}

program: decl* instr (EOL+ instr)* EOL* EOF;

decl: ID '<-' NUM COMMENT? EOL+ ;

instr: (label ':')? op # singleInstr
    | (label ':')? '[' EOL* op (EOL+ op)* EOL* ']' #instrList
    ;

/** Single operation. */
op: COMMENT #comment
    | opCode sources (('->'|'=>') targets)? ';'? COMMENT? #realOp
    ;

sources: (operand (',' operand)*)?;
targets: operand (',' operand)*;

/** Operation label. */
label: ID;

/** Operand: ID for label or register, number, string. */
operand: ID | NUM | SYMB | LAB | STR;

/** Opcode. */
opCode:
    // nop: placeholder
    'nop'

    /** Arithmetic. */

    // add r_1, r_2 => r_3: r_1 + r_2 => r_3
    | 'add'
    // sub r_1, r_2 => r_3: r_1 - r_2 => r_3
    | 'sub'
    // mult r_1, r_2 => r_3: r_1 * r_2 => r_3
    | 'mult'
    // div r_1, r_2 => r_3: r_1 / r_2 => r_3
    | 'div'
    // addI r_1, c_2 => r_3: r_1 + c_2 => r_3
    | 'addI'
    // subI r_1, c_2 => r_3: r_1 - c_2 => r_3
    | 'subI'
    // rsubI r_1, c_2 => r_3: c_2 - r_1 => r_3
    | 'rsubI'
    // multI r_1, c_2 => r_3: r_1 * c_2 => r_3
    | 'multI'
    // divI r_1, c_2 => r_3: r_1 / c_2 => r_3
    | 'divI'
    // rdivI r_1, c_2 => r_3: c_2 / r_1 => r_3
    | 'rdivI'

    /** Shifts. */

    // lshift r_1, r_2 => r_3: r_1 << r_2 => r_3
    | 'lshift'
    // lshift r_1, c_2 => r_3: r_1 << c_2 => r_3
    | 'lshiftI'
    // rshift r_1, r_2 => r_3: r_1 >> r_2 => r_3
    | 'rshift'
    // rshiftI r_1, c_2 => r_3: r_1 >> c_2 => r_3
    | 'rshiftI'

    /** Boolean Operations. */

    // and r_1, r_2 => r_3: r_1 AND r_2 => r_3
    | 'and'
    // andI r_1, c_2 => r_3: r_1 AND c_2 => r_3
    | 'andI'
    // or r_1, r_2 => r_3: r_1 OR r_2 => r_3
    | 'or'
    // orI r_1, c_2 => r_3: r_1 OR c_2 => r_3
    | 'orI'
    // xor r_1, r_2 => r_3: r_1 XOR r_2 => r_3
    | 'xor'
    // xorI r_1, c_2 => r_3: r_1 XOR c_2 => r_3
    | 'xorI'

    /** Memory Operations. */

    // loadI c_1 => r_2: c_1 => r_2
    | 'loadI'
    // load r_1 => r_2: Mem(r_1) => r_2
    | 'load'
    // loadAI r_1, c_2 => r_3: Mem(r_1 + c_2) => r_3
    | 'loadAI' // address-immediate
    // loadAO r_1, r_2 => r_3: Mem(r_1 + r_2) => r_3
    | 'loadAO' // address-offset
    // cload r_1 => r_2: character load
    | 'cload'
    // cloadAI r_1, c_2 => r_3: character loadAI
    | 'cloadAI'
    // cloadAO r_1, r_2 => r_3: character loadAO
    | 'cloadAO'

    // store r_1 => r_2: r_1 => Mem(r_2)
    | 'store'
    // storeAI r_1 => r_2, c_3: r_1 => Mem(r_2 + c_3)
    | 'storeAI'
    // storeAO r_1 => r_2, r_3: r_1 => Mem(r_2 + r_3)
    | 'storeAO'
    // cstore r_1 => r_2: character store
    | 'cstore'
    // cstoreAI r_1 => r_2, c_3: character storeAI
    | 'cstoreAI'
    // cstoreAO r_1 => r_2, r_3: character storeAO
    | 'cstoreAO'


    /** Register-to-Register Copy Operations. */

    // i2i r_1 => r_2: r_1 => r_2 for integers
    | 'i2i'
    // c2c r_1 => r_2: r_1 => r_2 for characters
    | 'c2c'
    // c2i r_1 => r_2: convert character to integer
    | 'c2i'
    // i2c r_1 => r_2: convert integer to character
    | 'i2c'

    /** Control-flow Operations. */

    // cmp_LT r_1, r_2 => r_3: true => r_3 if r_1 < r_2; false => r_3 otherwise
    | 'cmp_LT'
    // cmp_LE r_1, r_2 => r_3: true => r_3 if r_1 <= r_2; false => r_3 otherwise
    | 'cmp_LE'
    // cmp_EQ r_1, r_2 => r_3: true => r_3 if r_1 = r_2; false => r_3 otherwise
    | 'cmp_EQ'
    // cmp_GE r_1, r_2 => r_3: true => r_3 if r_1 >= r_2; false => r_3 otherwise
    | 'cmp_GE'
    // cmp_GT r_1, r_2 => r_3: true => r_3 if r_1 > r_2; false => r_3 otherwise
    | 'cmp_GT'
    // cmp_NE r_1, r_2 => r_3: true => r_3 if r_1 != r_2; false => r_3 otherwise
    | 'cmp_NE'
    // cbr r_1 -> l_2, l_3: l_2 -> PC if r_1 = true; l_3 -> PC otherwise
    | 'cbr'

    /** Alternate Comparison and Branch Syntax. */
    // comp r_1, r_2 => cc_3: sets cc_3. cc: condition code
    | 'comp'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = LT; l_3 -> PC otherwise
    | 'cbr_LT'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = LE; l_3 -> PC otherwise
    | 'cbr_LE'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = EQ; l_3 -> PC otherwise
    | 'cbr_EQ'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = GE; l_3 -> PC otherwise
    | 'cbr_GE'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = GT; l_3 -> PC otherwise
    | 'cbr_GT'
    // cbr_LT cc_1 -> l_2, l_3: l_2 -> PC if cc_1 = NE; l_3 -> PC otherwise
    | 'cbr_NE'

    /** Jumps. */
    // jump -> r_1: r_1 -> PC
    | 'jump'
    // jumpI -> l_1: l_1 -> PC
    | 'jumpI'
    // tbl r_1, l_2: r_1 might hold l_2
    | 'tbl'

    /** Stack Operations. */
    // push r_1: r_1 => Stack[SP], SP++
    | 'push'
    // pop => r_1: Stack[SP] => r_2, SP--
    | 'pop'
    // cpush r_1: character push
    | 'cpush'
    // cpop => r_1: character pop
    | 'cpop'

    /** I/O */

    // cin "xxx": read string literal and push onto stack
    | 'cin'
    // cout "xxx": write string literal
    | 'cout'

    /** SSA φ Function. */
    // phi r_i, r_j, r_k => r_m
    | 'phi'
  ;

/** Identifier. */
ID: LETTER (LETTER|DIGIT|[\-_])*;
/** Symbolic name. */
SYMB: '@' ID;
/** Label used as numeric parameter. */
LAB: '#' ID;
/** Number. */
NUM: '-'? DIGIT+;
/** String with optional escaped double quotes. */
STR : '"' (~["\n\r] | '\\"')* '"';
/** Comment. */
COMMENT: '//' ~[\r\n]*;
/** Whitespace. */
WS  : [ \t]+ -> skip;
EOL : [\r\n]+;

fragment LETTER: [a-zA-Z];
fragment DIGIT: [0-9];