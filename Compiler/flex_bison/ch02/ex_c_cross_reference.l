/* use symbol table to track c cross reference */
%option noyywrap nodefault yylineno

%x COMMENT
%x IFILE

/* some named patterns */
/* Universal Character Name */
UCN	(\\u[0-9a-fA-F]{4}|\\U[0-9a-fA-F]{8})
/* float exponent */
EXP ([Ee][-+]?[0-9]+)
/* integer length */
ILEN    ([Uu](L|l|LL|ll)?|(L|l|LL|ll)[Uu]?)

%{
#include "sym_tbl.h"

    /* include file stack */
    struct bufstack {
        struct bufstack *prev;
        YY_BUFFER_STATE bs;
        int lineno;
        char *filename;
        FILE *f;
    } *curbs;

    int newfile(char *fn);
    int popfile(void);

    int defining;                  /* names are probably definition*/
%}

%%
 /* comment */
"/*"                    { BEGIN COMMENT; }
<COMMENT>"*/"           { BEGIN INITIAL;}
<COMMENT>([^*]|\n)+|.
<COMMENT><<EOF>>        { printf("%s:%d: Unterminated comment\n", curfilename, yylineno); return 0; }
"//".*\n

 /* declaration keywords */
_Bool |
_Complex |
_Imaginary |
auto |
char |
const |
double |
enum |
extern |
float |
inline |
int |
long |
register |
restrict |
short |
signed |
static |
struct |
typedef |
union |
unsigned |
void |
volatite                                { defining = 1; }

break
case
continue
default
do
else
for
goto
if
return
sizeof
switch
while

 /* constants */

 /* integers */
0[0-7]*{ILEN}?
[1-9][0-9]*{ILEN}?
0[Xx][0-9a-fA-F]+{ILEN}?


 /* decimals */
([0-9]*\.[0-9]+|[0-9]+\.){EXP}?[flFL]?
[0-9]+{EXP}[flFL]?

 /* hex */
0[Xx]([0-9a-fA-F]*\.[0-9a-fA-F]+|[0-9a-fA-F]+\.?)[Pp][-+]?[0-9]+[flFL]?

 /* char */
\'([^'\\]|\\['"?\\abfnrtv]|\\[0-7]{1,3}|\\[Xx][0-9a-fA-F]+|{UCN})+\'

 /* string literal */
L?\"([^\"\\]|\\['"?\\abfnrtv]|\\[0-7]{1,3}|\\[Xx][0-9a-fA-F]+|{UCN})+\"

 /* punctuations */
"{"|"<%"|";"                            { defining = 0; }


"["|"]"|"("|")"|"{"|"}"|"."|"->"
"++"|"--"|"&"|"*"|"+"|"-"|"~"|"!"
"/"|"%"|"<<"|">>"|"<"|">"|"<="|">="|"=="|"!="|"^"|"|"|"&&"|"||"
"?"|":"|";"|"..."
"="|"*="|"/="|"%="|"+="|"-="|"<<="|">>="|"&="|"^=""|="
","|"#"|"##"
"<:"|":>"|"%>"|"%:"|"%:%:"

 /* identifier */
([_a-zA-Z]|{UCN})([_a-zA-Z0-9]|{UCN})*      { addref(yylineno, curfilename, yytext, defining); }

 /* whitespace */
[ \t\n]+

 /* continues line */
\\$

 /* preprocessor directives */
"#"" "*if.*\n
"#"" "*else.*\n
"#"" "*endif.*\n
"#"" "*define.*\n
"#"" "*line.*\n

 /* includes */
^"#"[ \t]*include[ \t]*[\"<]    { BEGIN IFILE; }
<IFILE>[^ \t\n\">]+             { 
                                    {
                                        int c;
                                        while ((c = input()) && c != '\n') ;
                                    }
                                    if (!newfile(yytext))
                                        yyterminate();
                                    BEGIN INITIAL;
                                }
<IFILE>.|\n                     { 
                                    fprintf(stderr, "%4d bad include line\n", yylineno);
                                    BEGIN INITIAL;
                                }
<<EOF>>                         { if(!popfile()) yyterminate(); }

 /* invalid character */
.                               { printf("%s:%d: Mystery character '%s'\n", curfilename, yylineno, yytext); }

%%

int newfile(char *fn) {
    FILE *f = fopen(fn, "r");
    struct bufstack *bs = malloc(sizeof(struct bufstack));

    if (!f) {
        perror(fn);
        return 0;
    }
    if (!bs) {
        perror("malloc");
        exit(1);
    }

    if (curbs) curbs->lineno = yylineno;
    bs->prev = curbs;

    bs->bs = yy_create_buffer(f, YY_BUF_SIZE);  /* setup current entry */
    bs->f = f;
    bs->filename = fn;
    yy_switch_to_buffer(bs->bs);
    
    curbs = bs;
    yylineno = 1;
    curfilename = fn;
    return 1;
}

int popfile(void) {
    struct bufstack *bs = curbs;
    struct bufstack *prevbs;

    if (!bs) return 0;

    fclose(bs->f);                          /* destroy current entry */
    yy_delete_buffer(bs->bs);

    prevbs = bs->prev;                      /* switch to previous */
    free(bs);

    if (!prevbs) return 0;

    yy_switch_to_buffer(prevbs->bs);
    curbs = prevbs;
    yylineno = curbs->lineno;
    curfilename = curbs->filename;
    return 1;
}

int main(int argc, char **argv) {
    int i;
    
    if (argc < 2) {
        fprintf(stderr, "need filename\n");
        return 1;
    }

    for (i = 1; i < argc; i++) {
        if (newfile(argv[i]))
            yylex();
    }

    printrefs();
    
    return 0;
}