%token <string> VALUE
%token LPAREN RPAREN
%token BSLASH
%token DOT
%token EOL
%token EOF
%start main             
%type <Expr.expr> main
%%
main:
  expression EOF                           { $1 }
;
expression:
  application BSLASH value DOT expression   { Expr.Application($1, Expr.Abstraction($3, $5)) }
  | BSLASH value DOT expression             { Expr.Abstraction($2, $4) }
  | application                             { $1 }
;
application:
  application atom                          { Expr.Application($1, $2)  }
  | atom                                    { $1 }
;
atom:
  LPAREN expression RPAREN                  { $2 }
  | value                                   { $1 }
;
value:
  VALUE                                     { Expr.Value $1 }
;
%%
