
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
  append(N5,N6,N7), sort(N7,N8), append(N2,N4,N9), sort(N9,N10),
  is_compat(N1,N4), is_compat(N2,N3), is_compat(N5,N6), is_compat(N2,N4) |
  impl(N8,N10).

%

impl(N1,N2) \ g(impl(N3,N4)) <=> subset(N1,N3), subset(N4,N2) | true.
g(_) <=> false.

%

reducesTo_(Goal, C) :-
  call(Goal),
  call(user:'$enumerate_constraints'(C)),
  writeln(C).
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

let rec pp_print_term ctx ppf t =
  let n, al = Swipl.extract_functor ctx t in
  match Swipl.show_atom n, al with
  | "n", [a] -> let i = Swipl.get_int ctx a |> Option.get in
    Format.fprintf ppf "n(%d)" i
  | "compat", [a1;a2] ->
    let i = Swipl.get_int ctx a1 |> Option.get in
    let j = Swipl.get_int ctx a2 |> Option.get in
    (*let i = match Swipl.get_int ctx a1 with | Some v -> v 
    | None -> match Swipl.get_int64 ctx a1 with Some v -> Int64.to_int v 
    | None -> match Swipl.get_long ctx a1 with Some v -> Signed.Long.to_int v 
    | None -> failwith "unexpected type" in
    let j = match Swipl.get_int ctx a2 with | Some v -> v 
    | None -> match Swipl.get_int64 ctx a2 with Some v -> Int64.to_int v 
    | None -> match Swipl.get_long ctx a2 with Some v -> Signed.Long.to_int v 
    | None -> failwith "unexpected type" in*)
    Format.fprintf ppf "compat(%d,%d)" i j
  | "impl", [a1;a2] -> 
    let l1 = Swipl.extract_list ctx a1 in
    let l2 = Swipl.extract_list ctx a2 in
    let l1 = List.map (fun a -> Swipl.get_int ctx a |> Option.get) l1 in
    let l2 = List.map (fun a -> Swipl.get_int ctx a |> Option.get) l2 in
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
  let ns = [M 1; M 2; M 3; M 4] in
  let cs = [Compat (1,2); Compat (1,4); Compat (2,3); Compat (3,4)] in
  let is = [Impl ([1;4],[3]); Impl ([2;3],[4])] in
  let g = Goal (Impl ([1;2],[3])) in
  let cs = ns @ cs @ is @ [g] in
  init ();
  Swipl.with_ctx ( fun ctx ->
    let cs = encode ctx cs in
    let res = Swipl.fresh ctx in    
    Swipl.call ctx (reducesTo cs res); 
    let _ = decode ctx res in ()
  );
  print_endline "done"

(* eof *)