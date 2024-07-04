exception NOT_UNIFIABLE
exception Not_Found
exception Program_Invalid
exception NotPossible

type variable = string and symbol = string
type signature = (symbol * int) list
type term = V of variable | Num of int | Node of symbol * (term list)
and  atom = A of symbol * (term list)
type substitution = (variable * term) list
type head = H of atom and body = B of atom list
type clause = F of head | R of head * body and program = clause list and goal = G of atom list

let union l1 l2 = List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) l2 l1


let rec variables_in_terms = function
  | V v -> [v]
  | Node (_, l) -> List.concat_map variables_in_terms l
  | _ -> []


let variables_in_atomic_formula (A(s, l)) = variables_in_terms (Node(s, l))

let rec vars_goal (G(g)) = List.fold_left union [] (List.map variables_in_atomic_formula g)


let rec subst s t =
  match t with
  | Node (s', l) -> Node (s', List.map (subst s) l)
  | _ -> (
    match t, s with
    | V x, (x', t') :: xs when x = x' -> t'
    | _ -> t
  )


let rec subst_atomic_formula s (A(s', l): atom) = A(s', List.map (subst s) l)


let rec occurs v t =
  match t with
      V(x) -> x = v
    | Node(s, l) -> List.fold_left (||) false (List.map (occurs v) l)
    | _ -> false


let compose (s1:substitution) (s2:substitution): substitution =
  let ss1 = List.map (fun x -> (fst x, subst s2 (snd x))) s1 in
  let ss2 = List.filter (fun x -> not (List.mem_assoc (fst x) s1)) s2 in
  ss1 @ ss2

  let rec mgu_term t1 t2 =
    match (t1, t2) with
    | (V x, V y) when x = y -> []
    | (V x, V y) -> [(x, t2)]
    | (V x, Node(_, _)) -> if occurs x t2 then raise NOT_UNIFIABLE else [(x, t2)]
    | (Node(_, _), V x) -> if occurs x t1 then raise NOT_UNIFIABLE else [(x, t1)]
    | (Num n1, Num n2) when n1 = n2 -> []
    | (Num n1, V x) -> [(x, t1)]
    | (V x, Num n2) -> [(x, t2)]
    | (Node(s1, l1), Node(s2, l2)) ->
       if s1 <> s2 || List.length l1 <> List.length l2 then
         raise NOT_UNIFIABLE
       else
         let rec mgu_helper l1 l2 s =
           match l1, l2 with
           | [], [] -> s
           | t1::r1, t2::r2 ->
              let substi1 = subst s t1
              and substi2 = subst s t2 in
              let mgu_subst = mgu_term substi1 substi2 in
              let s = compose s mgu_subst in
              mgu_helper r1 r2 s
           | _, _ -> raise NOT_UNIFIABLE
         in
         mgu_helper l1 l2 []
    | _ -> raise NOT_UNIFIABLE

let mgu_atom (A(s1, l1): atom) (A(s2, l2): atom): substitution = mgu_term (Node(s1, l1)) (Node(s2, l2))
;;
let rec modifyTerm (i:int) (t:term): term = match t with
    V(v) -> V((string_of_int i) ^ v)
  | Node(s, l) -> Node(s, List.map (modifyTerm i) l)
  | _ -> t
and  modifyAtom (i:int) (a:atom): atom = match a with
  A(s, l) -> A(s, List.map (modifyTerm i) l)
and  modifyInitialProg (prog:program) (i:int): program = 
  let rec modifyClause (cl:clause) (i:int): clause = match cl with
      F(H(a)) -> F(H(modifyAtom i a))
    | R(H(a), B(l)) -> R(H(modifyAtom i a), B(List.map (modifyAtom i) l)) 
  in  
  match prog with
    [] -> []
  | cl::ps -> (modifyClause cl i)::modifyInitialProg ps (i+1)
and  modifyProg2 (prog:program) (A(s, _): atom): program = 
  let rec modifyClause (cl:clause) (i:int): clause = match cl with
      F(H(a)) -> F(H(modifyAtom i a))
    | R(H(a), B(l)) -> R(H(modifyAtom i a), B(List.map (modifyAtom i) l))
in 
  match prog with
    [] -> []
  | cl::ps -> match cl with F(H(A(s', _))) | R(H(A(s', _)), _) ->
                if s = s' then (modifyClause cl 0)::modifyProg2 ps (A(s, []))
                else cl::modifyProg2 ps (A(s, []))
;;
let rec print_term (t: term) =
  match t with
  | V v -> Printf.printf " %s " v
  | Num n -> Printf.printf " %d " n
  | Node ("_empty", []) -> Printf.printf " [] "
  | Node (s, []) -> Printf.printf " %s " s  
  | Node ("_list", l) ->
     Printf.printf " [";
     print_list l;
     Printf.printf "] "
  | Node (s, l) ->
     Printf.printf " %s (" s;
     print_term_list l;
     Printf.printf ") "

and print_list l =
  let rec aux = function
    | [] -> ()
    | [t] -> print_term t
    | t :: ts ->
       print_term t;
       Printf.printf ",";
       aux ts
  in
  aux l

and print_term_list l = print_list l

let rec getsolution (unification) (vars)=
  let rec occurs l v =
    match l with
    | [] -> None
    | (x, t) :: xs ->
        if x = v then Some t
        else occurs xs v
  in
  match vars with
  | [] -> []
  | v :: vs ->
      match occurs unification v with
      | Some sol -> (v, sol) :: getsolution unification vs
      | None -> getsolution unification vs


let readCharbyChar () =
  let termio = Unix.tcgetattr Unix.stdin in
  let () = Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
          { termio with Unix.c_icanon = false } in
  let res = input_char stdin in
  Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
  res



let solve_atom_atom (a1) (a2) (unif) =
  compose unif (mgu_atom (subst_atomic_formula unif a1) (subst_atomic_formula unif a2))
;;

let eval a unif =
  let rec simplify_term = function
    | Num _ as t -> t
    | Node (op, [t1; t2]) ->
       let t1' = simplify_term (subst unif t1)
       and t2' = simplify_term (subst unif t2) in
       (match op, t1', t2' with
        | "+", Num n1, Num n2 -> Num (n1 + n2)
        | "-", Num n1, Num n2 -> Num (n1 - n2)
        | "*", Num n1, Num n2 -> Num (n1 * n2)
        | "/", Num n1, Num n2 when n2 <> 0 -> Num (n1 / n2)
        | _ -> raise NOT_UNIFIABLE)
    | t -> t
  in
  let eval_atom a =
    match a with
    | A(">", [t1; t2]) ->
       (match simplify_term t1, simplify_term t2 with
        | Num n1, Num n2 -> if n1 > n2 then unif else raise NOT_UNIFIABLE
        | _ -> raise NOT_UNIFIABLE)
    | A("<", [t1; t2]) ->
       (match simplify_term t1, simplify_term t2 with
        | Num n1, Num n2 -> if n1 < n2 then unif else raise NOT_UNIFIABLE
        | _ -> raise NOT_UNIFIABLE)
    | A("_eq", [t1; t2]) | A("_not_eq", [t1; t2]) ->
       compose unif (mgu_term (simplify_term t1) (simplify_term t2))
    | _ -> unif
  in
  eval_atom a


  let rec print_ans (unif:substitution) = match unif with
  [] -> Printf.printf "true. "
| [(v, t)] -> (
    Printf.printf "%s =" v;
    print_term t;
  )
| (v, t)::xs -> (
    Printf.printf "%s =" v;
    print_term t;
    Printf.printf ", ";
    print_ans xs;
  )
;;


let rec solve_goal prog g unif vars =
  match g with
  | G [] ->
    print_ans (getsolution unif vars);
    flush stdout;
    let rec read_choice () =
      let choice = readCharbyChar () in
      match choice with
      | '.' -> true, []
      | ';' -> false, []
      | _ ->
        flush stdout;
        read_choice ()
    in
    read_choice ()
  | G (a::gs) ->
    match a with    
    | A ("_not_eq", _) ->
      begin
        try false, eval a unif
        with NOT_UNIFIABLE -> solve_goal prog (G gs) unif vars
      end
    | A ("_cut", _) ->
      let _ = solve_goal prog (G gs) unif vars in
      true, []
    | A ("_eq", _) | A (">", _) | A ("<", _) ->
      begin
        try solve_goal prog (G gs) (eval a unif) vars
        with NOT_UNIFIABLE -> false, []
      end
    | _ ->
      let new_prog = modifyProg2 prog a in
      let rec iter prog' =
        match prog' with
        | [] -> false, []
        | cl::ps ->
          begin
            match cl with
            | F (H (a')) ->
              begin
                try
                  let u = solve_atom_atom a' a unif in
                  match solve_goal new_prog (G gs) u vars with
                  | true, u' -> true, u'
                  | _ -> iter ps
                with NOT_UNIFIABLE -> iter ps
              end
            | R (H (a'), B (al)) ->
              begin
                try
                  let u = solve_atom_atom a' a unif in
                  match solve_goal new_prog (G (al @ gs)) u vars with
                  | true, u' -> true, u'
                  | _ -> iter ps
                with NOT_UNIFIABLE -> iter ps
              end
          end
      in iter prog
;;


let interpret_goal prog g = solve_goal prog g [] (vars_goal g)
;;


let rec checkProgram prog = match prog with
    [] -> true
  | (F(H(a)))::xs | (R(H(a), _))::xs -> match a with
          A("_eq", _) | A("_not_eq", _) | A("_cut", _)
        | A(">", _) | A("<", _)-> raise Program_Invalid
        | _ -> checkProgram xs
;;