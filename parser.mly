%{
    open Interpreter
%}

%token DOT CUT RULESYM PIPE
%token LP RP LB RB COMMA EQ NOT_EQ 
%token PLUS MINUS TIMES DIV GT LT EOF


%left COMMA
%nonassoc EQ PIPE LT GT DOT
%left PLUS MINUS TIMES DIV


%token <string> VAR CONS
%token <int> NUM



%type <Interpreter.program> program
%type <Interpreter.goal> goal
%start program goal

%%

program:
    EOF                                 {[]}
  | clause_list EOF                     {$1}


clause_list:
// empty
  |  clause                              {[$1]}
  | clause clause_list                  {($1)::$2}
  |{[]}


clause:
    atomic_formula DOT                           {F(H($1))}
  | atomic_formula RULESYM atomic_formula_list DOT            {R(H($1), B($3))}


goal:
    atomic_formula_list DOT                      {G($1)}

atomic_formula_list:
    atomic_formula                                {[$1]}
  | atomic_formula COMMA atomic_formula_list                {($1)::$3}


atomic_formula:
    /* LP atomic_formula RP                          {$2} */
  | CONS LP terms RP                {A($1, $3)}
  | CONS                                {A($1, [])}
  | CUT                                 {A("_cut", [])}
  | term EQ term                        {A("_eq", [$1; $3])}
  | term NOT_EQ term                    {A("_not_eq", [$1; $3])}
  | term LT term                        {A("<", [$1; $3])}
  | term GT term                        {A(">", [$1; $3])}

list:
    LB RB                               {Node("_empty", [])}
  | LB term RB                         {Node("_list", [$2; Node("_empty", [])])}
  | LB term PIPE term RB          {Node("_list", [$2; $4])}
  | LB list_body RB                     {$2}


list_body:
  term COMMA list_body                 {Node("_list", [$1; $3])}

term:
  | primary_term                     { $1 }
  | list                             { $1 }


primary_term:
  | LP term RP                       { $2 }
  | VAR                              { V($1) }
  | NUM                              { Num($1) }
  | CONS                             { Node($1, []) }
  | CONS LP terms RP                 { Node($1, $3) }
  | term PLUS term                   { Node("+", [$1; $3]) }
  | term MINUS term                  { Node("-", [$1; $3]) }
  | term TIMES term                  { Node("*", [$1; $3]) }
  | term DIV term                    { Node("/", [$1; $3]) }

terms:
  | term COMMA terms                 { $1 :: $3 }
  | term                             { [$1] }
