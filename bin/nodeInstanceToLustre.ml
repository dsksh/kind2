open Lib
open NodeInstance

let pp_print_svi nno ppf sv =
  Format.fprintf ppf
    "%a : %a"
    (pp_print_svar_instance nno) sv
    (LustreExpr.pp_print_lustre_type true) (SV.type_of_state_var (fst sv))

let pp_print_prop nn v_map e_map header ppf p =
  let e0 = match SVT.find_opt e_map p.LustreContract.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  (*let svs = LustreExpr.state_vars_of_expr e0 in
  let svis = SVS.fold (fun sv l -> (instantiate_svar nn v_map sv)::l) svs [] in*)
  (*let expr = LustreExpr.map_vars (mk_subst_var (Some nn) v_map) e0 in*)
  let sco = Some (StateVar.scope_of_state_var (fst nn)) in
  let expr = LustreExpr.map_vars (mk_subst_var ~inherited:sco None v_map) e0 in
  Format.fprintf ppf "@[<hv 2>@ @ %s@ %a;@]@;" 
    header (LustreExpr.pp_print_lustre_expr false) expr

let pp_print_contract nodes ppf ni0 =
  let ppp_prop ni = pp_print_prop ni0.name ni.map ni.src.state_var_expr_map 
  in
  let ppp_a header ni = match ni.src.contract with
  | None -> ()
  | Some c -> 
    List.iter (ppp_prop ni header ppf) c.assumes 
  in
  let ppp_g header ni = match ni.src.contract with
  | None -> ()
  | Some c -> 
    let gs = fst (List.split c.guarantees) in
    List.iter (ppp_prop ni header ppf) gs 
  in
  (* Transfer the As and Gs from the children. *)
  let f ppp c_name = 
    match List.find_opt 
      (fun ni -> ni.name = c_name) nodes with
    | Some ni -> ppp ni
    | None -> failwith "child node not found" 
  in
  ppp_a "assume" ni0;
  List.iter (f (ppp_g "assume")) ni0.children;
  ppp_g "guarantee" ni0;
  List.iter (f (ppp_a "guarantee")) ni0.children

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