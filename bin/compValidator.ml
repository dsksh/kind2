open Lib
open NodeInstance

let init () = 
  Swipl.initialise ();
  Swipl.load_source {|
:- use_module(library(chr)).
:- use_module(library(lists)).
:- chr_option(debug, on).
:- chr_option(optimize, off).

:- chr_constraint compat/2, is_c/2, is_compat/2, n/1, impl/2, g/1, 
                  init/1, test/2, to_log/1, log/1.

to_log(I), log(L1) <=> append(L1,[I],L2) | log(L2), I.
to_log(_) <=> fail.

%

n(N) \ n(N) <=> true.

n(N) ==> compat(N,N).
compat(N,N) \ compat(N,N) <=> true.

is_compat([],_) <=> false.
is_compat(_,[]) <=> false.
is_compat([N1],NL2) <=> is_c(N1,NL2).
is_compat([N1|NL1],NL2) <=> is_c(N1,NL2), is_compat(NL1,NL2).

is_c(_,[]) <=> true.
compat(N1,N2) \ is_c(N1,[N2|NL2]) <=> is_c(N1,NL2).
compat(N2,N1) \ is_c(N1,[N2|NL2]) <=> is_c(N1,NL2).
is_c(_,_) <=> false.

%

impl(N1,N2) \ impl(N1,N2) <=> true.

impl(N1,N2), impl(N3,N4) ==>
  subtract(N1,N4,N5), subtract(N3,N2,N6), 
  is_compat(N5,N6), append(N5,N6,N7), sort(N7,N8), 
  is_compat(N2,N4), append(N2,N4,N9), sort(N9,N10) |
  impl(N8,N10).

%

impl(N1,N2) \ g(impl(N3,N4)) <=> subset(N1,N3), subset(N4,N2) | true.
%g(_) <=> false.

%

reducesTo_(Goal, C) :-
  call(Goal),
  call(user:'$enumerate_constraints'(C)).
reducesTo(Goal, Constraints) :-
  findall(Constraint, reducesTo_(Goal, Constraint), Constraints).
|} 

type smod = int

type t =
  | M of smod
  | Compat of smod * smod
  | Impl of smod list * smod list
  | Goal of t

let smod ctx i = 
  let i = Swipl.encode_integer ctx i in
  Swipl.Syntax.(app ("n" /@ 1) [i])
let compat ctx i j = 
  (*let i = smod ctx i in
  let j = smod ctx j in*)
  let i = Swipl.encode_integer ctx i in
  let j = Swipl.encode_integer ctx j in
  Swipl.Syntax.(app ("compat" /@ 2) [i; j])
let compat ctx i j = if i < j then compat ctx i j else compat ctx j i
let impl ctx i j = 
  let i, j = List.sort Int.compare i, List.sort Int.compare j in
  let i = Swipl.encode_list ctx (List.map (Swipl.encode_integer ctx) i) in
  let j = Swipl.encode_list ctx (List.map (Swipl.encode_integer ctx) j) in
  Swipl.Syntax.(app ("impl" /@ 2) [i; j])
let goal t = Swipl.Syntax.(app ("g" /@ 1) [t])

let rec encode ctx = function
| M i ->
  let i = Swipl.encode_integer ctx i in
  Swipl.Syntax.(app ("n" /@ 1) [i])
| Compat (i,j) when (i <= j) ->
  let i = Swipl.encode_integer ctx i in
  let j = Swipl.encode_integer ctx j in
  Swipl.Syntax.(app ("compat" /@ 2) [i; j])
| Compat (j,i) ->
  encode ctx (Compat (i,j))
| Impl (i,j) ->
  let i, j = List.sort Int.compare i, List.sort Int.compare j in
  let i = Swipl.encode_list ctx (List.map (Swipl.encode_integer ctx) i) in
  let j = Swipl.encode_list ctx (List.map (Swipl.encode_integer ctx) j) in
  Swipl.Syntax.(app ("impl" /@ 2) [i; j])
| Goal t ->
  let t = encode ctx t in
  Swipl.Syntax.(app ("g" /@ 1) [t])

let encode ctx cs =
  let cs = List.map (encode ctx) cs in
  let c :: cs = cs in
  List.fold_left Swipl.Syntax.(fun acc l -> Swipl.Syntax.(&&) acc l) c cs

let reducesTo goal result = Swipl.Syntax.(app ("reducesTo" /@ 2) [goal; result])

let rec pp_print_constr ppf = function
| M i -> Format.fprintf ppf "M(%d)" i
| Compat (i,j) -> Format.fprintf ppf "Compat(%d,%d)" i j
| Impl (i,j) -> 
  Format.fprintf ppf "Impl([%a], [%a])" 
    (Lib.pp_print_list Format.pp_print_int ",") i
    (Lib.pp_print_list Format.pp_print_int ",") j
| Goal c -> Format.fprintf ppf "G(%a)" pp_print_constr c

let rec pp_print_term ctx ppf t =
  let n, al = Swipl.extract_functor ctx t in
  match Swipl.show_atom n, al with
  | "n", [a] -> let i = Swipl.extract_int ctx a in
    Format.fprintf ppf "n(%d)" i
  | "compat", [a1;a2] ->
    let i = Swipl.extract_int ctx a1 in
    let j = Swipl.extract_int ctx a2 in
    Format.fprintf ppf "compat(%d,%d)" i j
  | "impl", [a1;a2] -> 
    let l1 = Swipl.extract_list ctx a1 in
    let l2 = Swipl.extract_list ctx a2 in
    let l1 = List.map (fun a -> Swipl.extract_int ctx a) l1 in
    let l2 = List.map (fun a -> Swipl.extract_int ctx a) l2 in
    Format.fprintf ppf "impl([%a], [%a])"
      (Lib.pp_print_list Format.pp_print_int ",") l1
      (Lib.pp_print_list Format.pp_print_int ",") l2
  | "g", [t] ->
    Format.fprintf ppf "g(%a)" (pp_print_term ctx) t
  | n, _ ->
    Format.fprintf ppf "%s/%d" n (List.length al)

let decode ctx t =
  (*Swipl.show_atom (Swipl.extract_atom ctx t)*)
  let n, a = Swipl.extract_name_arity ctx t in
  (*Format.printf "%s/%d\n" (Swipl.show_atom n) a;*)
  Format.printf "%a\n" (pp_print_term ctx) t
  (*Swipl.extract_list ctx t*)
let decode ctx t =
  let ls = Swipl.extract_list ctx t in
  List.map (decode ctx) ls

(*

let test () =
  init ();
  Swipl.with_ctx ( fun ctx ->
    let res = Swipl.fresh ctx in    
    let ns = List.map (fun i -> smod ctx i) [1; 2; 3; 4] in
    let cs = List.map (fun (i,j) -> compat ctx i j) [1,2; 1,4; 2,3; 3,4] in
    let is = [impl ctx [1;4] [3]; impl ctx [2;3] [4]] in
    let g = goal (impl ctx [1;2] [3]) in
    (*let g = impl ctx [1;2] [3] in*)
    (*let c :: cs = List.rev (ns @ cs @ is @ [g]) in*)
    let c :: cs = ns @ cs @ is @ [g] in
    let ls = List.fold_right Swipl.Syntax.(fun l acc -> Swipl.Syntax.(&&) l acc) cs c in
    Swipl.call ctx (reducesTo ls res); 
    (*Swipl.call ctx (Swipl.Syntax.(app ("writeln" /@ 1) [res]));*)
    let _ = decode ctx res in ()
  );
  print_endline "done"

let test1 () =
  let ns = [M 1; M 2; M (-3); M (-4)] in
  let cs = [Compat (1,2); Compat (1,-4); Compat (2,-3); Compat (-3,-4)] in
  let is = [Impl ([1;-4],[-3]); Impl ([2;-3],[-4])] in
  let g = Goal (Impl ([1;2],[-3])) in
  let cs = ns @ cs @ is @ [g] in
  init ();
  Swipl.with_ctx ( fun ctx ->
    let cs = encode ctx cs in
    let res = Swipl.fresh ctx in
    Swipl.call ctx (reducesTo cs res);
    let _ = decode ctx res in ()
  );
  print_endline "done"

*)

let is_compat_node_pair n1 n2 ps =
  let id1 = id_of_node_instance n1.name in
  let id2 = id_of_node_instance n2.name in
  if id1 < id2 then
    let ovs1 = instantiate_svar_trie n1.name n1.map n1.src.outputs in
    let ovs2 = instantiate_svar_trie n2.name n2.map n2.src.outputs in
    let chk v1 b = b && not (List.mem v1 ovs2) in
    if List.fold_right chk ovs1 true then
      Compat (id1, id2) :: ps
    else ps
  else ps

let is_compat_node_prop_pair n p ps =
  let id1 = id_of_node_instance n.name in
  let id2 = p.id in
  let ovs1 = instantiate_svar_trie n.name n.map n.src.outputs in
  let ovs2 = p.vars in
  let chk v1 b = b && not (List.mem v1 ovs2) in
  if List.fold_right chk ovs1 true then
    Compat (id2, id1) :: ps
  else ps

let is_compat_prop_pair p1 p2 ps =
  if p1.id < p2.id then
    let ovs1 = p1.vars in
    let ovs2 = p2.vars in
    let chk v1 b = b && not (List.mem v1 ovs2) in
    if List.fold_right chk ovs1 true then
      Compat (p1.id, p2.id) :: ps
    else ps
  else ps

let enum_compat_pairs cf np1 l2 ps =
  List.fold_right (cf np1) l2 ps
let enum_compat_pairs cf l1 l2 =
  List.fold_right (fun n -> enum_compat_pairs cf n l2) l1 []

let validate ns ps cs gs =
  let ids_m = List.map (fun n -> id_of_node_instance n.name) ns in
  let ms = List.map (fun i -> M i) ids_m in
  let ms = ms @ (List.map (fun p -> M p.id) ps) in
  Format.printf "%a@." (pp_print_list pp_print_constr ",@ ") ms;

  let compats = enum_compat_pairs is_compat_node_pair ns ns in
  let compats = compats @ (enum_compat_pairs is_compat_node_prop_pair ns ps) in
  let compats = compats @ (enum_compat_pairs is_compat_prop_pair ps ps) in
  Format.printf "%a@." (pp_print_list pp_print_constr ",@ ") compats;

  let impls = List.map 
    (fun (mid,ids_a,ids_a_i,ids_g,ids_g_i) -> Impl (ids_a @ ids_a_i @ [mid], ids_g @ ids_g_i)) cs in
  Format.printf "%a@." (pp_print_list pp_print_constr ",@ ") impls;
  (*let g_impls = List.map (fun (mid,ids_a,ids_g) -> Goal (Impl ((mid::ids_a), ids_g))) gs in*)
  let g_impls = List.map (fun (_,ids_a,ids_g) -> Goal (Impl (ids_a @ ids_m, ids_g))) gs in
  Format.printf "%a@." (pp_print_list pp_print_constr ",@ ") g_impls;

  let cs = ms @ compats @ impls @ g_impls in
  init ();
  Swipl.with_ctx ( fun ctx ->
    let cs = encode ctx cs in
    let res = Swipl.fresh ctx in
    Swipl.call ctx (reducesTo cs res);
    let _ = decode ctx res in ()
  );
  print_endline "done";
  true


(* eof *)