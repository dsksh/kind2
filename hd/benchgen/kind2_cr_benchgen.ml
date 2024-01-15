open Format
open Lib
open CompValidator

type node = 
  | N of int
  | C of int * node list

let id_of_node = function
| N i -> i
| C (i,_) -> i

(*type triple = int * node * int*)
(*let id_of_tuple (_, n, _) = id_of_node n*)

let rec pp_print_node ppf = function
| N i ->  Format.fprintf ppf "N%d" i
| C (i,ns) -> Format.fprintf ppf "N%d(%a)" i (pp_print_list pp_print_node ",") ns

let pp_print_prop ppf i = if i > 0 then Format.fprintf ppf "P%d" i

let pp_print_triple ppf (i, n, j) = 
  Format.fprintf ppf "{%a} %a {%a}" pp_print_prop i pp_print_node n pp_print_prop j

(* *)

type t = {
  id : int;
  children : int list;
  assume : (int * int) list;
  guarantee : (int * int) list;
}

let rec get_succ ts cs = 
  let f id acc = 
    match List.find_opt (fun t -> t.id = id) ts with
    | Some t -> 
      id::((get_succ ts t.children) @ acc)
    | None -> acc in
  List.fold_right f cs []

let pp_print_c ts ppf t =
  let ids = List.sort Int.compare (t.id::(get_succ ts t.children)) in
  Format.fprintf ppf "%a" 
    (pp_print_list (fun ppf -> Format.fprintf ppf "M%d") "*") ids

let pp_print_p ppf (i,j) =
  Format.fprintf ppf "P%d" (- i);
  let rec f k = if k > 0 then
    (Format.fprintf ppf "'"; f (k-1))
  in
  f j

let pp_print_t ts ppf t = Format.fprintf ppf "{%a} %a {%a}" 
  (pp_print_list pp_print_p "*") t.assume
  (pp_print_c ts) t
  (pp_print_list pp_print_p "*") t.guarantee

(* Enumerate the tpl_list content and apply f if all sub-nodes are processed. *)
let loop f t_tbl tpl_list =
  (*let tbl = Hashtbl.create (List.length tpl_list) in*)
  let rec g = function
  | ((_, N j, _) as t)::ts -> 
    let t = f t in
    Hashtbl.add t_tbl j t;
    g ts
  | ((_, C (j,cs), _) as t)::ts -> 
    let is_ready c_id = match Hashtbl.find_opt t_tbl c_id with
    | None -> false
    | Some _ -> true 
    in
    let cis = List.map id_of_node cs in
    if List.fold_right (fun c b -> b && is_ready c) cis true then
      let t = f t in
      Hashtbl.add t_tbl j t;
      g ts
    else
      g (ts @ [t])
  | [] -> ()
  in
  g tpl_list; ()

let parse m_tbl (i, n, j) =
  let id, cs = match n with
  | N k -> k, []
  | C (k,ns) -> 
    let is = List.map id_of_node ns in
    k, is
  in
  let m_idx idx = match Hashtbl.find_opt m_tbl idx with
  | None -> Hashtbl.add m_tbl idx 1; 0
  | Some k -> Hashtbl.replace m_tbl idx (k + 1); k
  in
  let _ = m_idx id in
  { id = id; children = cs; 
    assume = if i = 0 then [] else [- i, m_idx (- i)]; 
    guarantee = if j = 0 then [] else [- j, m_idx (- j)] }

let flatten t_tbl t =
  if t.children = [] then t
  else
    let inherit_ps c t =
      let c = Hashtbl.find t_tbl c in
      let a = t.assume @ c.guarantee in
      let g = t.guarantee @ c.assume in
      { t with assume = a; guarantee = g }
    in
    let tr = List.fold_right inherit_ps t.children t in
    tr

(* *)

let flatten_pid p_base (i,j) = if j <= 0 then i else i*p_base - j

let rec enum_compat_pairs ps0 = function
| m1::ms ->
  let ps1 = List.fold_right (fun m2 ps1 -> (Compat (m1,m2))::ps1) ms [] in
  enum_compat_pairs (ps0 @ ps1) ms
| [] -> ps0

let enum_compat_n_p_pairs p_base ps accum t = 
  let gs = List.map (flatten_pid p_base) t.guarantee in
  let f accum p = 
    (*printf "%d: %d v. %a@." t.id p (pp_print_list Format.pp_print_int ",") gs;*)
    if List.mem p gs then accum 
    else accum @ [(Compat (t.id,p))] in
  List.fold_left f accum ps

let to_cvt p_base ts t =
  let c = List.sort Int.compare (t.id::get_succ ts t.children) in
  let a = List.map (flatten_pid p_base) t.assume in
  let g = List.map (flatten_pid p_base) t.guarantee in
  (*let c = List.map (fun i -> M i) c in
  let a = List.map (fun i -> M i) a in
  let g = List.map (fun i -> M i) g in*)
  Impl (a @ c, g)

(* *)

let input = ref 0
let parse_input i = input := int_of_string i

let do_gen = ref true
let do_gen_smt = ref false
let verbose = ref false

let speclist = [
  ("-smt", Arg.Set do_gen_smt, "Generate in the SMT-LIB format");
  ("-v", Arg.Set verbose, "Turn on the verbose mode");
  ("-debug", Arg.Unit (fun () -> do_gen := false; verbose := true), "Turn on the debug mode");
]

let tcs = [
  [], (0, N 1, 1); (* 0; invalid *)
  [], (1, N 1, 2); (* 1; invalid *)
  [(0, N 1, 1)], (0, C (2, [N 1]), 1); (* 2; valid *)
  [(0, N 1, 1)], (0, C (2, [N 1]), 2); (* 3; valid *)
  [(1, N 1, 2)], (0, C (2, [N 1]), 2); (* 4 *)
  [(1, N 1, 2)], (1, C (2, [N 1]), 2); (* 5 *)
  [(0, N 1, 1)], (2, C (2, [N 1]), 3); (* 6 *)
  [(1, N 1, 2); (2, N 2, 1)], (0, C (3, [N 1; N 2]), 2); (* 7 *)
  [(0, N 1, 1); (0, N 2, 1)], (0, C (3, [N 1; N 2]), 1); (* 8 *)
  [(1, N 1, 2); (3, N 2, 4)], (0, C (3, [N 1; N 2]), 5); (* 9 *)
  [(1, N 1, 2); (1, N 2, 2)], (0, C (3, [N 1; N 2]), 1); (* 10 *)
  [(1, N 1, 2); (2, N 2, 1); (3, C (3, [N 1; N 2]), 1); (1, N 4, 3)], (0, C (5, [N 3; N 4]), 1); (* 11 *)
  [(1, N 1, 2); (2, N 2, 1); (1, N 3, 2)], (0, C (4, [N 1; N 2; N 3]), 1); (* 12 *)
  [(0, N 1, 1); (0, C (2, [N 1]), 1)], (0, C (3, [N 2]), 1); (* 13 *)
  [(0, N 1, 1); (1, N 2, 2); (0, N 3, 1)], (0, C (4, [N 1; N 2; N 3]), 1); (* 14 *)
]

let () = 
  Arg.parse speclist parse_input "benchgen [-smt] <integer>";

  let ass, goal = List.nth tcs !input in
  if !verbose then
    printf "%a@.@." (pp_print_list pp_print_triple ",@ ") (ass @ [goal]);

  let m_tbl = Hashtbl.create 7 in
  let t_tbl = Hashtbl.create 7 in
  loop (parse m_tbl) t_tbl (ass @ [goal]);
  let ts = Hashtbl.fold (fun _ t ts -> t::ts) t_tbl [] in
  let ts = List.sort (fun t1 t2 -> Int.compare t1.id t2.id) ts in
  (*let ass, goal = List.partition (fun t -> t.id = id_of_tuple goal) ts in*)
  let goal = List.nth ts ((List.length ts) - 1) in
  let ts = List.map (flatten t_tbl) ts in
  if !verbose then begin
    printf "%a,@ " (pp_print_list (pp_print_t []) ",@ ") ts;
    if List.length ts > 1 then printf "%a@." (pp_print_t ts) goal;
    printf "@."
  end;

  let vmax = Hashtbl.fold (fun _ j vmax -> if j > vmax then j else vmax) m_tbl 0 in
  let vmax = vmax - 1 in
  let rec pow10 e = if e = 0 then 10 else 10*pow10 (e-1) in
  let p_base = pow10 (vmax / 10) in
  let rec expand i j = if j < 0 then [] else (expand i (j-1)) @ [flatten_pid p_base (i,j)] in
  let ns, ps = Hashtbl.fold (fun i j acc -> ((i,j-1)::acc)) m_tbl []
    |> List.sort (fun m1 m2 -> Int.compare (fst m1) (fst m2))
    |> List.fold_left (fun acc (i,j) -> acc @ (expand i j)) []
    |> List.partition (fun m -> m >= 0) in
  let compats = enum_compat_pairs [] ns in
  let compats = enum_compat_pairs compats ps in
  let compats = List.fold_left (enum_compat_n_p_pairs p_base ps) compats ts in
  let ns = List.map (fun i -> M i) ns in
  let ps = List.map (fun i -> M i) ps in
  let goal = Goal (to_cvt p_base ts goal) in
  (*let ts = if List.length ts > 1 then List.map (to_cvt p_base []) ts else [] in*)
  let ts = List.map (to_cvt p_base []) ts in
  let cs = ns @ ps @ compats @ ts @ [goal] in
  if !verbose then
    printf "%a@.@." (pp_print_list pp_print_constr ",@,") cs;

  if !do_gen then begin
    if not !do_gen_smt then
      printf "%a@." pp_print_script cs
    else
      printf "%a@." CompValidatorSmt.pp_print_script cs
  end

  ;;