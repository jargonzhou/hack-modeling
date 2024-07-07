/* text concordance */
%option noyywrap nodefault yylineno case-insensitive

%{
#include "sym_tbl.h"
%}

%%

  /* skip common words */
a |
an |
and |
are |
as |
at |
be |
but |
for |
in |
is |
it |
of |
on |
or |
that |
the |
this |
to                /* ignore */

[a-z]+(\'(s|t))?  { addref(yylineno, curfilename, yytext, 0); }
.|\n              /* ignore everything else */

%%
int main(int argc, char **argv) {
  int i;
  if (argc < 2) {
    curfilename = "(stdin)";
    yylineno = 1;
    yylex();
  } else {
    for (i = 1; i < argc; i++) {
      FILE *f = fopen(argv[i], "r");
      if (!f) {
        perror(argv[1]);
        return 1;
      }
      curfilename = argv[i];

      yyrestart(f);
      yylineno = 1;
      yylex();
      fclose(f);
    }
  }

  printrefs();
}