open Lib
open NodeInstance

let pp_print_svi nno ppf sv =
  Format.fprintf ppf
    "%a : %a"
    (pp_print_svar_instance nno) sv
    (LustreExpr.pp_print_lustre_type true) (SV.type_of_state_var (fst sv))

let pp_print_prop nn v_map v_map_opt e_map header ppf p =
  let expr = match SVT.find_opt e_map p.LustreContract.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  Format.printf "processing %a; %a@." 
    (LustreExpr.pp_print_lustre_expr false) expr LustreContract.pp_print_svar p;
  let sco = Some (StateVar.scope_of_state_var (fst nn)) in
  let expr = LustreExpr.map_vars (mk_subst_var ~inherited:sco None v_map) expr in
  let expr = match v_map_opt with 
  | Some m -> LustreExpr.map_vars (mk_subst_var ~inherited:sco None m) expr
  | None -> expr in
  Format.fprintf ppf "@[<hv 2>@ @ %s@ %a;@]@;" 
    header (LustreExpr.pp_print_lustre_expr false) expr

let pp_print_contract nodes ppf ni0 =
  let ppp_prop is_local ni = 
    let m_opt = if is_local then None else Some ni0.map in
    pp_print_prop ni0.name ni.map m_opt ni.src.state_var_expr_map 
  in
  let ppp_a is_local header ni = match ni.src.contract with
  | None -> ()
  | Some c -> 
    List.iter (ppp_prop is_local ni header ppf) c.assumes 
  in
  let ppp_g is_local header ni = match ni.src.contract with
  | None -> ()
  | Some c -> 
    let gs = fst (List.split c.guarantees) in
    List.iter (ppp_prop is_local ni header ppf) gs 
  in
  (* Transfer the As and Gs from the children. *)
  let p_child ppp c_name = 
    match List.find_opt 
      (fun ni -> ni.name = c_name) nodes with
    | Some ni -> ppp ni
    | None -> failwith "child node not found" 
  in
  print_endline "p1";
  ppp_a true "assume" ni0;
  print_endline "p2";
  List.iter (p_child (ppp_g false "assume")) ni0.children;
  print_endline "p3";
  ppp_g true "guarantee" ni0;
  print_endline "p4";
  List.iter (p_child (ppp_a false "guarantee")) ni0.children

let pp_print_node nodes ppf ni =
  let { name; map; src; _ } = ni in
  let nno = Some name in
  let ivs = instantiate_svar_trie name map src.inputs in
  let ovs = instantiate_svar_trie name map src.outputs in
  let lvs = List.fold_left 
    (fun l lvs -> l @ (instantiate_svar_trie name (SVT.create 0) lvs))
    [] src.locals in
  let es = List.map ( fun ((v,bf),body) -> 
      (mk_subst_sv map v, bf), LustreExpr.map_vars (mk_subst_var None map) body )
    src.equations in
  Format.fprintf ppf
  "@[<hv 0>@[<hv 2>node %a (%a)@ returns (%a);@]@,\
  @[<v 0>(*@@contract@;%a*)@]@,\
  @[<hv 2>%s%a@]@,\
  let@,\
    @[<hv 2>@ @ %a@]@,\
  tel@]@."
    (pp_print_svar_instance None) name
    (pp_print_list (pp_print_svi nno) ";@ ") ivs
    (pp_print_list (pp_print_svi nno) ";@ ") ovs
    (pp_print_contract nodes) ni
    (if lvs = [] then "" else "var ")
    (fun ppf -> (List.iter (Format.fprintf ppf "%a;@ " (pp_print_svi nno)))) lvs
    (pp_print_list (LustreNode.pp_print_node_equation false) "@;") es

let pp_print_nodes ppf nodes =
  List.iter (fun n -> Format.fprintf ppf "%a@." (pp_print_node nodes) n) (List.rev nodes)

(* *)