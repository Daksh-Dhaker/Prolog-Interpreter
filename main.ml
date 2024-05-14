open Lexer
open Parser
open Types

type subst = Normal of (string*term) list | Compos of subst list;;
exception NOT_UNIFIABLE of string;;
exception NO_ANSWERS_FOUND of string;;
exception ANSWERS_FOUND of string;;

let rec print_term = function
  | Variable v -> Printf.printf "%s" v
  | Constant c -> Printf.printf "%s" c
  | Int c -> Printf.printf "%d" c
  | Function (f, args) ->
    Printf.printf "Function(%s, " f;
    print_term_list args;
    print_string ")"
  | Set (a) -> Printf.printf "" ;
    print_term_list a;
    print_string ""
  | Pipe(a,b) -> 
    Printf.printf "" ;
    print_term_list ([a;b]);
    print_string ""

and print_term_list_aux = function
  | [] -> ()
  | [t] -> print_term t
  | t::ts -> print_term t; print_string "; "; print_term_list_aux ts

and print_term_list terms = 
  print_string "[";
  print_term_list_aux terms;
  print_string "]"

let rec print_atomic_formula = function

  | Predicate (p,terms) ->
      Printf.printf "Atomic_formula(%s, " p;
      print_term_list terms;
      print_string ")"


let rec print_body = function
        | [] -> ()
        | [af] -> print_atomic_formula af
        | af::afs -> print_atomic_formula af;Printf.printf ","; print_body afs

let print_clause = function
  | Fact f ->
    print_string "Fact(";
    print_atomic_formula f;
    print_string ")\n"
  | Rule (head, body) ->
    print_string "Rule(";
    print_atomic_formula head;
    print_string ", Body[";
    print_body body;
    print_string "])\n"

let print_program program =
  List.iter print_clause program

let set_union xs ys =
  let rec add_if_not_present acc x =
    if List.mem x acc then acc else x :: acc
  in
  List.fold_left add_if_not_present ys xs;;

let rec vars f = 
  match f with 
  | Variable x -> [x]
  | Constant c -> []
  | Int c -> []
  | Function(a,b) -> (List.fold_left (set_union) [] (List.map vars b))
  | Set(b) -> (List.fold_left (set_union) [] (List.map vars b))
  | Pipe(a,b) -> (List.fold_left (set_union) [] (List.map vars ([a;b])))

let rec vars_for_at l =
  match l with
  | [] -> []
  | Predicate(a,terms)::tl -> (List.fold_left (set_union) [] (List.map vars terms)) @ (vars_for_at tl)

let rec subst sigma t =

  let rec search lst elem =
    match lst with
    | [] -> Variable elem
    | (x, y) :: tl ->
        if x = elem then
          y 
        else
          search tl elem
        in 
  
  match t with
  | Variable x -> search sigma x
  | Constant a -> Constant a 
  | Int a -> Int a
  | Function (a,b) -> Function (a,List.map (subst sigma) b)
  | Set a -> Set (List.map (subst sigma) a)
  | Pipe (a,b) -> Pipe(subst sigma a,subst sigma b)
;;

let rec subst2 sigma t = 
  match sigma with 
  | Normal lst -> subst lst t 
  | Compos lst -> match lst with 
                  | [] -> t
                  | hd::tl -> subst2 (Compos tl) (subst2 hd t)

let rec subst_atomic_formula sigma at =
  match at with
  | Predicate (a,l) -> Predicate (a,List.map (subst2 sigma) l)

let rec mgu t1 t2 = 
  match t1, t2 with
  | Variable x, Variable y ->  Normal [(x, Variable y)]
  | Variable x, Constant a -> Normal [(x,Constant a)]
  | Variable x, Int a -> Normal [(x,Int a)]
  | Variable x, Function (a,b) ->let vars2 = vars (Function(a,b)) in 
                              if (List.mem x vars2) then begin
                                raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                              end else 
                                Normal [(x , Function (a,b))]
  | Variable x, Pipe(a,b) -> let vars2 = vars (Function("",[a;b])) in 
                              if (List.mem x vars2) then begin
                                raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                              end else 
                                Normal [(x , Pipe (a,b))]
  | Pipe(a,b),Variable x -> let vars2 = vars (Function("",[a;b])) in 
                                if (List.mem x vars2) then begin
                                  raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                                end else 
                                  Normal [(x , Pipe (a,b))]
  | Variable x, Set(a) -> let vars2 = vars (Set(a)) in
                              if (List.mem x vars2) then begin
                                raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                              end else 
                                Normal [(x , Set(a))]
  | Constant a, Variable x -> Normal[(x,Constant a)]
  | Constant a, Constant b -> if (a = b) then begin
                                Normal []
                              end else
                                raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Constant a, Int b -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Constant a, Function (c,d) -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Constant a, Set b -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Int a, Variable x -> Normal[(x,Int a)]
  | Int a, Constant b -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Int a, Int b -> if (a = b) then begin
                      Normal []
                    end else
                      raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Int a, Function(c,d) -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Int a, Set b -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Function (a,b), Variable x -> let vars2 = vars (Function(a,b)) in 
                                  if (List.mem x vars2) then begin
                                    raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                                  end else 
                                    Normal [(a , Function (a,b))]
  | Function (a,b), Constant c -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Function (a,b), Set c -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Function (a,b), Int c -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Function (a,b),Function(c,d)-> 
    if a = c then begin
      if List.length b = List.length d then begin
        if List.length b = 0 then
          Normal []
        else
          let rec helper tl1 tl2 sub =
            match tl1, tl2 with
            | [], [] -> sub
            | hd1::tail1, hd2::tail2 -> let s1 = [sub]@[mgu (subst2 sub hd1) (subst2 sub hd2)] in 
                                        helper tail1 tail2 (Compos s1)

            | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
          in
          let s1 = mgu (List.hd b) (List.hd d) in
          helper (List.tl b) (List.tl d) s1
      end else
        raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
    end else
      raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Set a, Variable x -> let vars2 = vars (Set(a)) in
                              if (List.mem x vars2) then begin
                                raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                              end else 
                                Normal [(x , Set(a))]
  | Pipe (a1,b1),Pipe(c1,d1) ->
                    let b = [a1;b1] in
                    let d = [c1;d1] in 
                    if List.length b = List.length d then begin
                      if List.length b = 0 then
                        Normal []
                      else
                        let rec helper tl1 tl2 sub =
                          match tl1, tl2 with
                          | [], [] -> sub
                          | hd1::tail1, hd2::tail2 -> let s1 = [sub]@[mgu (subst2 sub hd1) (subst2 sub hd2)] in 
                                                      helper tail1 tail2 (Compos s1)

                          | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                        in
                        let s1 = mgu (List.hd b) (List.hd d) in
                        helper (List.tl b) (List.tl d) s1
                    end else
                      raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Pipe(a,b),Set c ->
                      if List.length c = 0 then begin
                        raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                      end else
                        let hd::tl = c in
                        Compos ([(mgu a hd);(mgu b (Set tl))])

  | Set c,Pipe(a,b) -> 
                       if List.length c = 0 then begin
                        raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                      end else
                        let hd::tl = c in
                        Compos ([(mgu a hd);(mgu b (Set tl))])
  | Set a, Constant c -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Set a, Int c -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Set a, Function (c,d) -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | Set b,Set d -> if List.length b = List.length d then begin
                      if List.length b = 0 then
                        Normal []
                      else
                        let rec helper tl1 tl2 sub =
                          match tl1, tl2 with
                          | [], [] -> sub
                          | hd1::tail1, hd2::tail2 -> let s1 = [sub]@[mgu (subst2 sub hd1) (subst2 sub hd2)] in 
                                                      helper tail1 tail2 (Compos s1)

                          | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                        in
                        let s1 = mgu (List.hd b) (List.hd d) in
                        helper (List.tl b) (List.tl d) s1
                    end else
                      raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
  | _,_ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")

    

let rec unify_formula at1 at2 =
  match at1, at2 with
  | Predicate(a,b),Predicate(c,d) ->
    if a = c then begin
      if List.length b = List.length d then begin
        if List.length b = 0 then
          Normal []
        else
          let rec helper tl1 tl2 sub =
            match tl1, tl2 with
            | [], [] -> sub
            | hd1::tail1, hd2::tail2 -> let s1 = [sub]@[mgu (subst2 sub hd1) (subst2 sub hd2)] in 
                                        helper tail1 tail2 (Compos s1)

            | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
          in
          let s1 = mgu (List.hd b) (List.hd d) in
          helper (List.tl b) (List.tl d) s1
      end else
        raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
    end else
      raise (NOT_UNIFIABLE "NOT_UNIFIABLE")

let rec modifyterm i t =
  match t with
  | Variable v -> Variable((string_of_int i) ^ v)
  | Constant c -> Constant c
  | Int a -> Int a 
  | Function(s,l) ->Function(s,List.map (modifyterm i) l)
  | Set s -> Set (List.map (modifyterm i) s)
  | Pipe (a,b) -> Pipe(modifyterm i a,modifyterm i b)
;;

let rec modifyatom i a =
  match a with
  Predicate(s,l) -> Predicate(s,List.map (modifyterm i) l)

let rec modifyclause cl i =
  match cl with
  | Fact(at) -> Fact(modifyatom i at)
  | Rule(at,bd) -> Rule(modifyatom i at,(List.map (modifyatom i) bd)) 

let rec modifyprog2 program at =
  let Predicate(a,_) = at in
  match program with
  | [] -> []
  | cl::ps -> match cl with Fact(Predicate(s',_)) | Rule(Predicate(s',_),_) ->
                if a = s' then (modifyclause cl 1)::(modifyprog2 ps (Predicate(a,[])))
                else cl::(modifyprog2 ps (Predicate(a,[])))

let rec simplifyterm t =
  match t with
  | Int a -> Int a 
  | Function("+",[t1;t2]) -> (match (simplifyterm t1,simplifyterm t2) with
                              (Int n1,Int n2) -> Int(n1+n2)
                              | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | Function("-",[t1;t2]) -> (match (simplifyterm t1,simplifyterm t2) with
                              (Int n1,Int n2) -> Int(n1-n2)
                              | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | Function("*",[t1;t2]) -> (match (simplifyterm t1,simplifyterm t2) with
                              (Int n1,Int n2) -> Int(n1*n2)
                              | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | Function("/",[t1;t2]) -> (match (simplifyterm t1,simplifyterm t2) with
                              (Int n1,Int n2) -> Int(n1/n2)
                              | _ -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | _ -> t
;;

let rec eval at sub =
  match at with
  | Predicate("eq",[t1;t2]) -> Compos [sub;(mgu (simplifyterm (subst2 sub t1)) (simplifyterm (subst2 sub t2)))]
  | Predicate("not_eq",[t1;t2]) -> Compos [sub;(mgu (simplifyterm (subst2 sub t1)) (simplifyterm (subst2 sub t2)))]
  | Predicate("gte",[t1;t2]) -> (match (simplifyterm (subst2 sub t1),simplifyterm (subst2 sub t2)) with
                                  (Int n1,Int n2) -> if n1 > n2 then sub else raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                                  | _ ->  raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | Predicate("lte",[t1;t2]) -> (match (simplifyterm (subst2 sub t1),simplifyterm (subst2 sub t2)) with
                                  (Int n1,Int n2) -> if n1 < n2 then sub else raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
                                  | _ ->  raise (NOT_UNIFIABLE "NOT_UNIFIABLE"))
  | _ -> sub


let getchoice () =
    print_string "Enter choice : ";
    flush stdout;
    let line = input_line stdin in
    if String.length line >= 1 then
      line.[0]
    else
      failwith "No input found";;

let rec print_subst_lst lst = 

        let rec print_subst sub =
          match sub with
          | Normal l ->     (*print_string("(Normal(");*)
                            let rec helper lst =
                              match lst with
                              | []-> print_string("")
                              | (a,b)::tl -> print_string(a);
                                             print_string(" = ");
                                             print_term(b);
                                             print_string("\n");
                                             helper tl
                            in 
                            helper l;
                            (*print_string(")),")*)
          | Compos l -> (*print_string ("(compos(");*)
                        let rec print_compos_lst cmps_lst =
                          match cmps_lst with
                          | [] -> (*print_string (")),")*)
                                  print_string("")
                          | hd::tl -> print_subst_lst cmps_lst 
                        in
                        print_compos_lst l
                        
        in
      
        match lst with
        | [] -> print_string ("")
        | hd::tl -> print_subst hd;
                    print_subst_lst tl
      ;;
      
let rec print_subst_main sub =
        match sub with
        | Normal l ->     (*print_string("(Normal(");*)
                          let rec helper lst =
                            match lst with
                            | []-> print_string("")
                            | (a,b)::tl -> print_string(a);
                                           print_string(" = ");
                                           print_term(b);
                                           print_string("\n");
                                           helper tl
                          in 
                          helper l;
                          (*print_string(")),")*)
        | Compos l -> (*print_string ("(compos(");*)
                      let rec print_compos_lst cmps_lst =
                        match cmps_lst with
                        | [] -> (*print_string (")),")*)
                                print_string("")
                        | hd::tl -> print_subst_lst cmps_lst 
                      in
                      print_compos_lst l


let rec print_subst_main2 sub vars_list =
  
  let rec apply_until v =
    let l = subst2 sub (v) in
    match l with
    | v -> print_term(v);
          print_string(",")
    | Int a-> print_int(a);
              print_string(",")
    | Constant a -> print_string(a);
                    print_string(",")
    | Function (a,b) -> print_string("Function(");
                        print_string("a,[");
                        List.map apply_until b;
                        print_string("]),")
    | Set b -> print_string("");
                        print_string("[");
                        List.map apply_until b;
                        print_string("],")

    | Pipe (a,b) -> print_string("[");
                    apply_until a;
                    print_string(",");
                    apply_until b;
                    print_string("]")
        
                        
  in


  
  match vars_list with
  | [] -> print_string("")
  | hd::tl -> print_term(Variable(hd));
              print_string(" = ");
              apply_until (Variable(hd));
              print_string("\n");
              print_subst_main2 (sub) tl

let rec backtracking goal_list program_list =

  let rec matching goal_lst program_lst sub goal_og program_og arg  =
    (* print_body(goal_lst);
    print_string("\n");
    print_program(program_lst);
    print_string("\n");
    print_string("----------"); *)
    match goal_lst, program_lst with
    | [],_ -> print_subst_main2 (sub) (vars_for_at (goal_list));
              print_string("true.\n");
        flush stdout;
        let command_usr = ref (getchoice()) in
        while(!command_usr <> '.' && !command_usr <> ';') do
          Printf.printf "\nUnwanted character: %c \n? " (!command_usr);
          flush stdout;
          command_usr := getchoice();
        done;
        Printf.printf "\n";
        if !command_usr = '.' then sub
        else begin
          if arg = 1 then
            raise ( ANSWERS_FOUND "NOT_UNIFIABLE")
          else
            raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
        end

    | hd::tl,[] -> raise (NOT_UNIFIABLE "NOT_UNIFIABLE")
    | Predicate("!",terms)::tlg,hdc::tlc -> let _ = (matching tlg program_og sub goal_og program_og 1) in (sub)
                                            
                                            (* print_string("here"); *)

    | Predicate("fail",terms)::tlg, hdc::tlc -> raise (NO_ANSWERS_FOUND "NO_ANSWERS_FOUND")
    | Predicate("gte",terms)::tlg,hdc::tlc -> matching tlg program_og (eval (Predicate("gte",terms)) sub) goal_og program_og 0         
    | Predicate("eq",terms)::tlg,hdc::tlc -> matching tlg program_og (eval (Predicate("eq",terms)) sub) goal_og program_og 0
    | Predicate("not_eq",terms)::tlg,hdc::tlc -> matching tlg program_og (eval (Predicate("not_eq",terms)) sub) goal_og program_og 0
    | Predicate("lte",terms)::tlg,hdc::tlc -> matching tlg program_og (eval (Predicate("lte",terms)) sub) goal_og program_og 0
    | hdg::tlg, hdc::tlc -> (*print_program (program_lst);*)
                            (* print_body (goal_lst);
                            print_string("\n");
                            print_string("-----------------------\n"); *)
                            match hdc with
                            | Fact at ->  
                                                if try (unify_formula (subst_atomic_formula sub hdg) (subst_atomic_formula sub at); true) with _ -> false then
                                                  let u1 = unify_formula (subst_atomic_formula sub hdg) (subst_atomic_formula sub at) in
                                                  let sub_temp = Compos (sub::[u1])in
                                                  
                                                  try
                                                    (* print_string("B\n"); *)
                                                    let new_prog = (modifyprog2 program_og hdg) in
                                                    let ans_temp = (matching tlg new_prog sub_temp goal_og new_prog 0) in
                                                    ans_temp
                                                    
                                                  with
                                                  | ANSWERS_FOUND c -> raise (ANSWERS_FOUND "NOT_UNIAFIABLE")
                                                  | _ ->
                                                        (matching goal_lst tlc sub goal_og program_og 0)
                                                        
                                                else
                                                  
                                                  let t_ans = (matching goal_lst tlc sub goal_og program_og 0) in
                                                  (* print_string("D\n"); *)
                                                  t_ans
                                                  
                                                  
                                          
                            | Rule (hd,bd) -> 
                                              if try (unify_formula (subst_atomic_formula sub hdg) (subst_atomic_formula sub hd); true) with _ -> false then
                                                  let u1 = unify_formula (subst_atomic_formula sub hdg) (subst_atomic_formula sub hd) in
                                                  let sub_temp = Compos (sub::[u1])in
                                                  
                                                  try
                                                    (* print_string("B\n"); *)
                                                    let new_prog = (modifyprog2 program_og hdg) in
                                                    let modify_bd = List.map (subst_atomic_formula sub_temp) bd in
                                                    let ans_temp = (matching (modify_bd@tlg) new_prog sub_temp goal_og new_prog 0) in
                                                    ans_temp
                                                    
                                                  with
                                                  | ANSWERS_FOUND c -> raise (ANSWERS_FOUND "NOT_UNIAFIABLE")
                                                  | _ ->
                                                        (matching goal_lst tlc sub goal_og program_og 0)
                                                        
                                                else
                                                  
                                                  let t_ans = (matching goal_lst tlc sub goal_og program_og 0) in
                                                  (* print_string("D\n"); *)
                                                  t_ans
                                              (* try (* if head unifies *)
                                              
                                              let u1 = unify_formula (subst_atomic_formula sub hdg) (subst_atomic_formula sub hd) in
                                              (* print_string("Reached here"); *)
                                              let sub_temp = Compos (sub::[u1]) in
                                              let new_prog = (modifyprog2 program_og hdg) in 
                                              
                                                try (* if body resolves *)
                                                  let body_resol = (matching bd new_prog sub_temp goal_og new_prog) in
                                                  try
                                                    print_string("E\n");
                                                    let ans_temp = (matching tlg new_prog body_resol goal_og new_prog) in 
                                                    ans_temp
                                                  with
                                                    | _ -> print_string("T\n");
                                                      (matching goal_lst tlc sub goal_og program_og)
                                                with
                                                  | _ -> print_string("F\n");
                                                    (matching goal_lst tlc sub goal_og program_og)
                                              with
                                                | _ -> print_string("TY\n");
                                                  (matching goal_lst tlc sub goal_og program_og)
                                               *)
                            
  in
  
  (matching goal_list program_list (Normal []) goal_list program_list 0)
;;




let main =
  while true do
    try
      print_string ("Enter the program: \n");
      let input_program = read_line() in
      let lexbuf1 = Lexing.from_string input_program in
      let program_list = Parser.program Lexer.token lexbuf1 in
      print_string ("Enter the goal: \n");
      let input_goal = read_line() in 
      let lexbuf2 = Lexing.from_string input_goal in
      let goal_list = Parser.body Lexer.token lexbuf2 in
      print_string("Resolution: \n");
      try
        
        (backtracking goal_list program_list);
        print_string("true\n")
      with
      | Parsing.Parse_error ->
        print_string("false.");
      | _ -> print_string("false.");
      print_string("\n")

    with End_of_file -> ()
  done


(* Test cases

1.  h(1).h(2).
Enter the program: 
h(1).h(2).
Enter the goal:
h(X).
Resolution:
X = 1,
true.
Enter choice : ;

X = 2,
true.
Enter choice : ;

false.
------------------
2. 
mem(1).void(A,B):-mem(A),mem(B).mem(3).
Enter the goal:
void(C,D).
Resolution:
C = 1,
D = 1,
true.
Enter choice : ;

C = 1,
D = 3,
true.
Enter choice : ;

C = 3,
D = 1,
true.
Enter choice : ;

C = 3,
D = 3,
true.
Enter choice : ;

false.
--------------------------------
3. mem(X,[]) :- fail.mem(X,[X|R]) :- !.mem(X,[Y|R]) :- mem(X,R). 
Enter the goal:
mem(3,[1,2,3]).
Resolution:
true.
Enter choice : ;

false.
----------------------------
4. del(X,[],[]):- !.del(X,[X|R],Z):- del(X,R,Z),!.del(X,[Y|R],[Y|Z]):- del(X,R,Z),!.
Enter the goal:
del(1,[1,2,3,4],T).
Resolution:
T = [2; [3; [4; []]]],
true.
Enter choice : ;

false.
----------------------------
5. Enter the program:
del(X,[],[]):- !.del(X,[X|R],Z):- del(X,R,Z),!.del(X,[Y|R],[Y|Z]):- del(X,R,Z),!.
Enter the goal:
del(3,[1,2,3,4],T).
Resolution:
T = [1; [2; [4; []]]],
true.
Enter choice : ;

false.
-------------------------------
6. Enter the program:
inter([],[],[],S2):- !.inter([],S2,[],S2):- !.inter([X|Y],[],Z,S2):- inter(Y,S2,Z,S2),!.inter([X|R1],[X|R2],[X|Z],S2):- inter(R1,S2,Z,S2),!.inter([X|R1],[Y|R2],Z,S2):- inter([X|R1],R2,Z,S2).interI(S1,S2,S3):- inter(S1,S2,S3,S2).
Enter the goal:
interI([1,2,3,4,5],[5,77,3,23,1,4],U).                                                                                                 
Resolution: 
U = [1; [3; [4; [5; []]]]],
true.
Enter choice : ;

false.
-----------------------------------
7. Enter the program:
set_diff([],[],[],S2):- !.set_diff([],S2,[],S2):- !.set_diff([X|Y],[],[X|Z],S2):- set_diff(Y,S2,Z,S2),!.set_diff([X|R1],[X|R2],Z,S2):- set_diff(R1,S2,Z,S2),!.set_diff([X|R1],[Y|R2],Z,S2):- set_diff([X|R1],R2,Z,S2).diffI(S1,S2,S3):- set_diff(S1,S2,S3,S2).
Enter the goal:
diffI([1,2,3,4,66,34],[3,2,4,9,10],T).                                                                                                 
Resolution: 
T = [1; [66; [34; []]]],
true.
Enter choice : ;

false.
----------------------------------
8. ft(0,1).ft(X1,Y1):-X1>0,Z1=X1-1,ft(Z1,W1),Y1=W1*X1.
Enter the goal:
ft(7,B).
Resolution:
B = 5040,
true.
Enter choice : ;

false.
------------------------------------
9. Enter the program:
likes(john, mary).likes(john, trains).likes(peter, fast_cars).likes(Person1, Person2):- hobby(Person1, Hobby), hobby(Person2, Hobby).hobby(john, trainspotting).hobby(tim, sailing).hobby(helen, trainspotting).hobby(simon, sailing).
Enter the goal:
likes(john,X).
Resolution:
X = mary,
true.
Enter choice : ;

X = trains,
true.
Enter choice : ;

X = john,
true.
Enter choice : ;

X = helen,
true.
Enter choice : ;

false.
-----------------------------
10.likes(john, mary).likes(john, trains).likes(peter, fast_cars).likes(Person1, Person2):- hobby(Person1, Hobby), hobby(Person2, Hobby).hobby(john, trainspotting).hobby(tim, sailing).hobby(helen, trainspotting).hobby(simon, sailing).
Enter the goal:
likes(peter,X).                                                                                                                        
Resolution: 
X = fast_cars,
true.
Enter choice : ;

false.

*)
