{
    open Parser
    type tok = VARIABLE of string | CONSTANT of string | INT of int | BOOL of bool
                |OFCOURSE of string | FAIL of string
}

rule token = parse 
    | [' ' '\t' '\n']                                       { token lexbuf }
    | "("                                                   { LPAREN }
    | ")"                                                   { RPAREN }
    | ","                                                   { COMMA "and" }
    | "&&"                                                  { AND_term "and"}
    | "."                                                   { DOT }
    | ":-"                                                  { COLON_MINUS }
    | "!"                                                   { OFCOURSE "!" }
    | "fail"                                                { FAIL "fail" } 
    | "["                                                   { SET_OPEN }
    | ']'                                                   { SET_CLOSE }
    | "+"                                                   { ADD }
    | "-"                                                   { SUB }
    | "*"                                                   { MUL }
    | "/"                                                   { DIV }
    | "/+"                                                  { NOT_eq }
    | "="                                                   { Equal }
    | ">"                                                   { Gte }
    | "<"                                                   { Lte }
    | "|"                                                   { PIPE }                
    | ['A'-'Z'](['a'-'z''A'-'Z''0'-'9''_'])* as lxm         { VARIABLE lxm }
    | ['a'-'z'](['a'-'z''A'-'Z''0'-'9''_'])* as lxm         { CONSTANT lxm }
    | ['0'-'9']['0'-'9']* as lxm                            { INT(int_of_string lxm) }
    | eof                                                   { EOF }