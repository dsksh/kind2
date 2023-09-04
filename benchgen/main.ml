open Format
open Lib

type node = 
  | N of int
  | C of int * node list

let id_of_node = function
| N i -> i
| C (i,_) -> i

(*type triple = int * node * int*)

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

let pp_print_p ppf (i,j) =
  Format.fprintf ppf "P%d" i;
  let rec f k = if k > 0 then
    (Format.fprintf ppf "'"; f (k-1))
  in
  f j

let pp_print_t ppf t = Format.fprintf ppf "{%a} M%d {%a}" 
  (pp_print_list pp_print_p "*") t.assume
  t.id
  (pp_print_list pp_print_p "*") t.guarantee

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

let parse p_tbl (i, n, j) =
  let id, cs = match n with
  | N k -> k, []
  | C (k,ns) -> 
    let is = List.map id_of_node ns in
    k, is
  in
  let p_idx idx = match Hashtbl.find_opt p_tbl idx with
  | None -> Hashtbl.add p_tbl idx 1; 0
  | Some k -> Hashtbl.replace p_tbl idx (k + 1); k
  in
  { id = id; children = cs; 
    assume = if i = 0 then [] else [i, p_idx i]; 
    guarantee = if j = 0 then [] else [j, p_idx j] }

let flatten t_tbl t =
  (*let t = { t with guarantee = index_g g_tbl t.guarantee } in*)
  if t.children = [] then t
  else
    let inherit_ps c t =
      let c = Hashtbl.find t_tbl c in
      (*printf "%a@." pp_print_t c;*)
      let a = t.assume @ c.guarantee in
      let g = t.guarantee @ c.assume in
      { t with assume = a; guarantee = g }
    in
    List.fold_right inherit_ps t.children t

let tcs = [
  [(1, N 1, 2); (0, C (2, [N 1]), 2)];
  [(1, N 1, 2); (1, C (2, [N 1]), 2)];
  [(1, N 1, 2); (2, N 2, 1); (0, C (3, [N 1; N 2]), 2)];
  [(0, N 1, 1); (0, N 2, 1); (0, C (3, [N 1; N 2]), 1)];
  [(0, N 1, 1); (0, C (2, [N 1]), 1); (0, C (3, [N 2]), 1)];
  [(0, N 1, 1); (1, N 2, 2); (0, N 3, 1); (0, C (4, [N 1; N 2; N 3]), 1)];
]

let () = 
  (*printf "%a@.@." (pp_print_list pp_print_triple ",@ ") ex2;*)

  let tc = List.nth tcs 5 in

  let p_tbl = Hashtbl.create 7 in
  let t_tbl = Hashtbl.create 7 in
  loop (parse p_tbl) t_tbl tc;
  let ts = Hashtbl.fold (fun _ t ts -> t::ts) t_tbl [] in
  let ts = List.sort (fun t1 t2 -> Int.compare t1.id t2.id) ts in
  let ts = List.map (flatten t_tbl) ts in
  printf "%a@." (pp_print_list pp_print_t ",@ ") ts

  ;;