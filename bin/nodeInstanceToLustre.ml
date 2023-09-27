open Lib
open NodeInstance

let pp_print_svi nno ppf sv =
  Format.fprintf ppf
    "%a : %a"
    (pp_print_svar_instance nno) sv
    (LustreExpr.pp_print_lustre_type true) (SV.type_of_state_var (fst sv))

let pp_print_prop nn v_map e_map header ppf p =
  let expr = match SVT.find_opt e_map p.LustreContract.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  Format.printf "processing %a; %a@." 
    (LustreExpr.pp_print_lustre_expr false) expr LustreContract.pp_print_svar p;
  let sco = Some (StateVar.scope_of_state_var (fst nn)) in
  let expr = LustreExpr.map_vars (mk_subst_var ~inherited:sco None v_map) expr in
  (*let expr = match v_map_opt with 
  | Some m -> LustreExpr.map_vars (mk_subst_var ~inherited:sco None m) expr
  | None -> expr in *)
  Format.fprintf ppf "@[<hv 2>@ @ %s@ %a;@]@;" 
    header (LustreExpr.pp_print_lustre_expr false) expr

let pp_print_contract nodes ppf ni0 =
  let ppp_prop ni = pp_print_prop ni0.name ni.map ni.src.state_var_expr_map 
  in
  let ppp_a header ni = match ni.src.contract with
  | None -> ()
  | Some c -> List.iter (ppp_prop ni header ppf) c.assumes 
  in
  let ppp_g header ni = match ni.src.contract with
  | None -> ()
  | Some c -> let gs = fst (List.split c.guarantees) in
    List.iter (ppp_prop ni header ppf) gs 
  in
  (* Transfer the As and Gs from the children. *)
  let p_child ppp c_name = 
    match List.find_opt 
      (fun ni -> ni.name = c_name) nodes with
    | Some ni -> ppp ni
    | None -> failwith "child node not found" 
  in
  print_endline "p1";
  ppp_a "assume" ni0;
  print_endline "p2";
  List.iter (p_child (ppp_g "assume")) ni0.children;
  print_endline "p3";
  ppp_g "guarantee" ni0;
  print_endline "p4";
  List.iter (p_child (ppp_a "guarantee")) ni0.children

let pp_print_call ni map ppf = function 
  (* Node call on the base clock *)
  | (*{ call_node_name; 
      call_cond = [];
      call_inputs; 
      call_oracles; 
      call_outputs } ->*)
    call when call.LustreNode.call_cond = [] ->
      let nno = Some ni.name in
      let ivs = instantiate_svar_trie ni.name map call.LustreNode.call_inputs in
      let ovs = instantiate_svar_trie ni.name map call.LustreNode.call_outputs in
      Format.fprintf ppf
        "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>%a@,(%a);@]@]"
        (pp_print_list (pp_print_svar_instance nno) ",@ ") ovs
        (pp_print_svar_instance None) (instantiate_node_name call.LustreNode.call_node_name 0)
        (pp_print_list (pp_print_svar_instance nno) ",@ ") ivs

  | _ -> failwith "unsupported"

let pp_print_annot nodes ppf ni =
  if id_of_node_instance ni.name > 0 then
    Format.fprintf ppf "@[<v 0>(*@@contract@;%a*)@]@," (pp_print_contract nodes) ni
  else
    Format.fprintf ppf "@[<v 0>(* no contract *)@]"

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
  let calls = List.filter 
    ( fun c -> List.find_opt 
        (fun ni -> ni.name = instantiate_node_name c.LustreNode.call_node_name 0) nodes
      <> None )
    src.calls in
  Format.fprintf ppf
  "@[<hv 0>@[<hv 2>node %a (%a)@ returns (%a)@]@,\
  %a\
  @[<hv 2>%s%a@]@,\
  @[<hv 2>let@ \
    %a@ %a@]@,\
  tel@]@."
    (pp_print_svar_instance None) name
    (pp_print_list (pp_print_svi nno) ";@ ") ivs
    (pp_print_list (pp_print_svi nno) ";@ ") ovs
    (pp_print_annot nodes) ni
    (if lvs = [] then "" else "var ")
    (fun ppf -> (List.iter (Format.fprintf ppf "%a;@ " (pp_print_svi nno)))) lvs
    (pp_print_list (LustreNode.pp_print_node_equation false) "@;") es
    (pp_print_list (pp_print_call ni map) "@;") calls

let pp_print_nodes ppf nodes =
  let _ = List.fold_right ( fun n acc -> 
    if List.find_opt (fun n1 -> n1.name = n.name) acc = None then
      Format.fprintf ppf "%a@." (pp_print_node nodes) n else ();
    n::acc ) 
    nodes [] in ()

(* *)