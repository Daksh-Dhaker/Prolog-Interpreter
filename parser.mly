%token <string> VARIABLE CONSTANT OFCOURSE FAIL IF COMMA AND_term IS 
%token LPAREN RPAREN DOT COLON_MINUS ANYTHING THEN ELSE NOT SET_OPEN SET_CLOSE PIPE ADD SUB MUL DIV MOD NOT_eq Gte Lte Equal NOT_eq
%token <char> ERROR
%token EOF
%token <int> INT
%start body
%type <Types.body> body
%start program
%type <Types.program> program
%%

program:
    | clauses EOF {$1}

clauses:
    | /*empty*/  {[]}
    | clause DOT clauses {$1::$3}

clause:
    | fact { Fact $1}
    | rule { $1 }

fact:
    | atomic_formula { $1 }

rule:
    | atomic_formula COLON_MINUS body { Rule ($1,$3)}

body:
    | atomic_formula_list {$1}

atomic_formula_list:
    | atomic_formula {[$1]}
    | atomic_formula COMMA atomic_formula_list {$1::$3}

atomic_formula:
    | CONSTANT LPAREN term_list RPAREN                                          {Predicate($1,$3)}
    | CONSTANT                                                                  {Predicate($1,[])}
    | CONSTANT LPAREN RPAREN                                                    {Predicate($1,[])}
    | OFCOURSE                                                                  {Predicate($1,[])}
    | FAIL                                                                      {Predicate($1,[])}
    | term Gte term                                                             {Predicate("gte",[$1; $3])}
    | term Equal term                                                           {Predicate("eq",[$1; $3])}
    | term Lte term                                                             {Predicate("lte",[$1; $3])}
    | term NOT_eq term                                                          {Predicate("not_eq",[$1; $3])}


term_list:
    | term {[$1]}
    | term COMMA term_list {$1::$3}

term:
    | VARIABLE { Variable $1}
    | CONSTANT { Constant $1}
    | INT      { Int $1 }
    | CONSTANT LPAREN term_list RPAREN { Function($1,$3) }
    | CONSTANT LPAREN RPAREN { Function($1,[]) }
    | SET_OPEN term_list SET_CLOSE { Set($2) }
    | SET_OPEN SET_CLOSE { Set([]) }
    | SET_OPEN term PIPE term SET_CLOSE { Pipe($2,$4)}
    | term ADD term                     { Function("+",[$1;$3]) }
    | term SUB term                     { Function("-",[$1;$3]) }
    | term MUL term                     { Function("*",[$1;$3]) }
    | term DIV term                     { Function("/",[$1;$3]) }
    