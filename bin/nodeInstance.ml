open Lib
open LustreNode
open LustreContract

module I = LustreIdent 
module D = LustreIndex
module SV = StateVar
module SVS = StateVar.StateVarSet
module SVT = StateVar.StateVarHashtbl

type svar_instance = SV.t * int

type node_instance = { 
  name : svar_instance;  
  map : svar_instance SVT.t;
  children : svar_instance list;
  src : LustreNode.t;
}

type prop = {
  id : int;
  vars : svar_instance list;
  expr : LustreExpr.t;
}

let instantiate_node_name name id =
  let s = LustreIdent.string_of_ident false name in
  SV.mk_state_var "instance" [s] (Type.mk_int ()), id

let id_of_node_instance name = snd name

let hd_of_scope sv = 
  match SV.scope_of_state_var sv with
  | s::_ -> s
  | [] -> ""

let pp_print_scope_hd ppf (sv,id) =
  match SV.scope_of_state_var sv with
  | s::_ -> 
    Format.fprintf ppf "%s_%d__" s id
  | [] -> ()

let instantiate_svar (nn,id) map sv =
  match SVT.find_opt map sv with
  | Some svi -> svi
  | None -> 
    ( (* Create a local name e.g. Self_id__v. *)  
      let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
      (SV.type_of_state_var sv) in
      sv, id )

let instantiate_svar_trie nn map t =
  D.bindings t |> List.map (fun (_, sv) -> instantiate_svar nn map sv)

let register_arg map (nn,id) svar0 svar =
  (* Map CN.usr.v to PN_id__v. *)  
  SVT.add map svar0 (instantiate_svar (nn,id) map svar)

(* If id <> 0, append the scope to the name. *)
let mk_sv_from_svi ?(is_const:bool = false) (sv,id) =
  (*Format.printf "msfs %a %d@." SV.pp_print_state_var sv id;*)
  (*let ss = Format.asprintf "%a" pp_print_scope_hd (sv,id) in*)
  let ss = if id > 0 then Format.asprintf "%a" pp_print_scope_hd (sv,id) else "" in
  SV.mk_state_var ~is_const:is_const 
    (ss^(SV.name_of_state_var sv)) (SV.scope_of_state_var sv) (SV.type_of_state_var sv)

let mk_subst_sv map sv =
  match SVT.find_opt map sv with
  | Some svi -> mk_sv_from_svi svi
  | None -> sv

(*let mk_subst_e e_map var =
  let sv = Var.state_var_of_state_var_instance var in
  let e : LustreExpr.t = match SVT.find_opt e_map sv with
  | Some e -> e
  | None -> LustreExpr.mk_free_var var in
  Var.mk_var e
  *)

let mk_subst_var ?(inherited = None) nno map var =
  let mk_svar sv =
    KEvent.log L_debug "%a: " StateVar.pp_print_state_var sv;
    (*let ic = SV.is_const sv in*)
    let ic = false in
    match SVT.find_opt map sv with
    | Some (sv,id) -> ( 
        KEvent.log L_debug "%a is found@." StateVar.pp_print_state_var sv;
        match inherited with
        | Some sc -> 
          (* Case of getting a property inherited from a child instance (who manages the map) to 
             a parent instance (inherited). Omit printing the scope. *)
          (*if SV.scope_of_state_var sv = sc then*)
          if List.length sc > 0 && List.hd sc = hd_of_scope sv then
            (*let sv = SV.mk_state_var ~is_const:ic (SV.name_of_state_var sv) [] (SV.type_of_state_var sv) in*)
            let sv = SV.mk_state_var ~is_const:ic (SV.name_of_state_var sv) sc (SV.type_of_state_var sv) in
            sv, 0
          else sv, id
        | None -> sv, id
      )
    | None -> ( 
        KEvent.log L_debug "not found@.";
        match nno with
        | Some (nn,id) -> (
          (* Create a local name e.g. Self___id.v. *)  
          (*let sv = SV.mk_state_var ~is_const:ic (SV.name_of_state_var sv) (SV.scope_of_state_var nn) (SV.type_of_state_var sv) in*)
          sv, id )
        | None -> (
          (*let sv = SV.mk_state_var (SV.name_of_state_var sv) [] (SV.type_of_state_var sv) in*)
          sv, 0 )
      )
  in
  if Var.is_const_state_var var then
    let sv = Var.state_var_of_state_var_instance var in
    (*Format.printf "sv: %a@." SV.pp_print_state_var_debug sv;*)
    let svi = mk_svar sv in
    (*Format.printf "svi: %a@." SV.pp_print_state_var_debug (mk_sv_from_svi ~is_const:true svi);*)
    Var.mk_const_state_var (mk_sv_from_svi ~is_const:true svi)
  else if Var.is_state_var_instance var then
    let sv = Var.state_var_of_state_var_instance var in
    let svi = mk_svar sv in
    let o = Var.offset_of_state_var_instance var in
    Var.mk_state_var_instance (mk_sv_from_svi svi) o
  else (* is_free_var *)
    failwith "subst_var w/ free var"

let add_sv_to_trie v t =
  (* If a trie contains only a leaf w/ the key [], remake the trie. *)
  let t = if D.mem [] t then D.empty |> D.add [D.ListIndex 0] (D.find [] t) else t in
  let n = D.top_max_index t |> succ in
  let i = if n > 0 then [D.ListIndex n] else [] in (* TODO: adequacy of the index *)
  (*Format.printf "%a; %d@." (pp_print_list (D.pp_print_index true) ",") (D.keys t) n;
  Format.printf "@[%a@]@." (D.pp_print_index_trie true SV.pp_print_state_var) t;*)
  D.add i v t

(* *)

(*let add_ghost_vs node =
  let i = ref 0 in
  let f _ iv (os, cs) =
    let ff k civ acc = 
      if civ <> iv then acc else
        let os, cinputs = acc in
        let new_civ = SV.mk_state_var 
          (Format.sprintf "%s_ghost%d" (SV.name_of_state_var iv) !i)
          (SV.scope_of_state_var iv) (SV.type_of_state_var iv) in
        incr i;
        let os = add_sv_to_trie new_civ os in
        os, (k, new_civ)::cinputs
      in
    let os, new_cinputs = 
      List.fold_right 
        (fun c (os,cinputs) -> let os, cis = D.fold ff c.call_inputs (os,[]) in os, cis::cinputs) 
        cs (os,[]) in
    let ff (c,new_cis) =
      let cis = List.fold_right (fun (k,civ) cis -> D.add k civ cis) new_cis c.call_inputs in
      { c with call_inputs = cis } in
    let cs = List.map ff (List.combine cs new_cinputs) in
    os, cs
  in
  let os, cs = D.fold f node.inputs (node.outputs, node.calls) in
  { node with outputs = os; calls = cs }
*)

(* *)

(* Make some local variables observable (as input or output variables). *)
let mk_observable cs node =
  let f _ v (is,os,ls) = let n = SV.name_of_state_var v in
    if String.starts_with ~prefix:"call" n then
      (* Obtain the node_call. *)
      match List.find_opt 
        ( fun c -> List.find_opt (fun v1 -> v1 = v) (D.values c.call_outputs) <> None ) 
        node.calls with
      | Some c -> 
        (* Check if annotated... *)
        ( match List.find_opt (fun ci -> ci.name = instantiate_node_name c.call_node_name 0) 
          cs with
          | Some _ -> is, os, add_sv_to_trie v ls 
          | None -> (* it is annotated. *)
            add_sv_to_trie v is, os, ls )
      | None -> is, os, add_sv_to_trie v ls
    else if not (String.starts_with ~prefix:"sofar" n) && 
            not (String.starts_with ~prefix:"glocal" n) then
      is, add_sv_to_trie v os, ls
    else 
      is, os, add_sv_to_trie v ls in
  let ff ls (is,os,l) = 
    let is, os, ls = D.fold f ls (is, os, D.empty) in
    is, os, ls::l in
  let is, os, ls = List.fold_right ff node.locals (node.inputs, node.outputs, []) in
  { node with inputs = is; outputs = os; locals = ls; }

(* Returns an instance with a list of ancesters, and the latest id. *)
let rec instantiate_node nodes id map node =
  let nm = instantiate_node_name node.LustreNode.name id in
  KEvent.log L_debug "Instantiating node %a@." (LustreIdent.pp_print_ident true) node.name;
  let cs, cs_all, id = List.fold_right (instantiate_child nodes nm map) node.calls ([],[],id) in
  let c_ns = List.map (fun c -> c.name) cs in
  let node = if id > 0 then mk_observable cs node else node in
  let n = { name = nm; map = map; children = c_ns; src = node } in
  n, cs @ cs_all, id

(* Returns a list of direct children, a list of ancesters, and the latest id. *)
and instantiate_child nodes p_name map c (cs0, cs_all0, id) =
  (* Obtain the child node entry. *)
  let callee = LustreNode.node_of_name c.call_node_name nodes in
  match id, callee.contract with
  | id, Some _ when id > 0 -> 
    (* A binding map. *)
    let map = SVT.copy map in
    (* Prepare the binding map. *)
    let _ = List.combine (D.bindings callee.inputs) (D.bindings c.call_inputs) |> 
      List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
    let _ = List.combine (D.bindings callee.outputs) (D.bindings c.call_outputs) |> 
      List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
    let ci, cs, id = instantiate_node nodes (id+1) map callee in
    cs0 @ [ci], cs @ cs_all0, id

  | _, _ -> (* If the parent or this child is not annotated... *)
    (*let nm = instantiate_node_name callee.LustreNode.name 0 in
    let ci = { name = nm; map = map; children = []; src = callee } in*)
    let ci, cs, _ = instantiate_node nodes 0 map callee in
    cs0 @ [ci], cs @ cs_all0, id

let instantiate_main_nodes nodes =
  let map = SVT.create 7 in
  let f n (ns,id) = 
    if n.is_main then (
      ( if n.contract = None then
          let m = Format.asprintf "A main node w/ no contract: %a" 
            (LustreIdent.pp_print_ident false) n.name in 
          failwith m );
      let n, cs, id = instantiate_node nodes (id+1) map n in 
      n::cs, id )
    else ns, id in
  List.fold_right f nodes ([],0)

let get_prop_rhs nn v_map e_map p =
  (* Obtain the rhs expression. *)
  let expr = match SVT.find_opt e_map p.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in

  (*if Var.is_const_state_var var then
    let sv = Var.state_var_of_state_var_instance var in
    (*Format.printf "sv: %a@." SV.pp_print_state_var_debug sv;*)
    let svi = mk_svar sv in
    (*Format.printf "svi: %a@." SV.pp_print_state_var_debug (mk_sv_from_svi ~is_const:true svi);*)
    Var.mk_const_state_var (mk_sv_from_svi ~is_const:true svi)
  else if Var.is_state_var_instance var then
    *)

  (* Expand further the rhs if variables are registered in e_map. *)
  let expr = Var.VarSet.fold ( fun v expr ->
    let sv = Var.state_var_of_state_var_instance v in
    match SVT.find_opt e_map sv with
    | Some e -> 
      (*Format.printf "subst %a w/ %a@." SV.pp_print_state_var sv (LustreExpr.pp_print_lustre_expr false) e;*)
      let e = if Var.is_state_var_instance v then
          (* Inherit the offset. *)
          let o = Var.offset_of_state_var_instance v in
          LustreExpr.unsafe_expr_of_term (Term.bump_state o 
            (LustreExpr.unsafe_term_of_expr e.LustreExpr.expr_init)) 
        else e.LustreExpr.expr_init in 
      LustreExpr.apply_subst [v, e] expr
    | None -> expr )
    (LustreExpr.vars_of_expr expr) expr in

  (*Format.printf "res: %a@." (LustreExpr.pp_print_lustre_expr false) expr;*)

  (* Collect and instantiate variables. *)
  let svs = LustreExpr.state_vars_of_expr expr in
  let svis = SVS.fold (fun sv l -> (instantiate_svar nn v_map sv)::l) svs [] in

  (* Subst variables according to the node instantiation. *)
  (*let expr = LustreExpr.map_vars (mk_subst_var (Some nn) v_map) expr in*)
  let sco = Some (StateVar.scope_of_state_var (fst nn)) in
  let expr = LustreExpr.map_vars (mk_subst_var ~inherited:sco None v_map) expr in

  expr, svis

let collect_props get_rhs p (ps,pids) =
  let expr, svis = get_rhs p in
  match List.find_opt (fun p -> LustreExpr.equal p.expr expr) ps with
  | Some p -> ps, List.sort (fun i j -> -(Int.compare i j)) (p.id::pids)
  | None -> 
      let id = -1 - (List.length ps) in
      ps @ [{ id = id; vars = svis; expr = expr }], pids @ [id]

let collect_props_from_contract ni (ps,cs,goals) =
  match ni.src.contract with
  | None -> ps, cs, goals
  | Some c -> 
    let f = collect_props (get_prop_rhs ni.name ni.map ni.src.state_var_expr_map) in
    let ps,pids_a = List.fold_right f c.assumes (ps,[]) in
    let gs = fst (List.split c.guarantees) in
    let ps,pids_g = List.fold_right f gs (ps,[]) in 
    let pid = id_of_node_instance ni.name in
    let goals = if ni.src.is_main then (pid, pids_a, pids_g)::goals else goals in

    (* Transfer the As and Gs from the children. *)
    let f cn (a0, g0) = 
      match List.find_opt (fun (pid,_,_,_,_) -> pid = id_of_node_instance cn) cs with
    | None -> (a0, g0)
    | Some (_,a,_,g,_) -> (g @ a0, a @ g0) in
    let pids_a_i, pids_g_i = List.fold_right f ni.children ([],[]) in

    let c = pid, pids_a, pids_a_i, pids_g, pids_g_i in
    ps, c::cs, goals

let translate_subsystems in_sys =
  let ns = InputSystem.retrieve_lustre_nodes in_sys in
  (*let ns = List.map add_ghost_vs ns in*)
  KEvent.log L_info "Instantiating nodes";
  let nis, _ = instantiate_main_nodes ns in
  KEvent.log L_info "Collecting property nodes";
  let ps, cs, gs = List.fold_right collect_props_from_contract nis ([],[],[]) in
  (nis, ps, cs, gs)

(* *)

let pp_print_svar_instance nno ppf (sv,id) =
  let b = match nno with
  | Some (nn,id0) ->
    if hd_of_scope sv <> hd_of_scope nn || id <> id0 then true else false
  | None -> true in
  if b then (
    (*let pr ppf (s,id) = Format.fprintf ppf "%s___%d" s id in
    Format.fprintf ppf "%a__"
      (pp_print_list pr "__") (List.combine (SV.scope_of_state_var sv) id)*)
    (*match SV.scope_of_state_var sv with
    | s::sl -> 
      Format.fprintf ppf "%s_%a__" s 
      (pp_print_list Format.pp_print_int ",") id
      (*(pp_print_list Format.pp_print_string "_") sl*)
    | [] -> ()*)
    Format.fprintf ppf "%a" pp_print_scope_hd (sv,id)
    );
  Format.fprintf ppf "%s" (SV.name_of_state_var sv)

let pp_print_svi_typed nno ppf sv =
  Format.fprintf ppf
    "('%a', '%a')"
    (pp_print_svar_instance nno) sv
    Type.pp_print_type (SV.type_of_state_var (fst sv))

let pp_print_map nno ppf map =
  SVT.iter 
    ( fun v0 v1 -> Format.fprintf ppf "@[<hv 2>%s =@ %a;@ @]"
      (SV.name_of_state_var v0)
      (pp_print_svar_instance nno) v1 )
    map

let pp_print_node ppf { name; map; children; src } =
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
  "@[<v 2>'%a' : {@ \
    'ivs' : [@[<hv>%a@]],@ \
    'ovs' : [@[<hv>%a@]],@ \
    'lvs' : [@[<hv>%a@]],@ \
    'body' : [@[<hv>%a@]],@ \
    'children' : [@[<hv>%a@]],@ \
    'map' : [@[<hv>%a@]] }@]"
    (pp_print_svar_instance None) name
    (pp_print_list (pp_print_svi_typed nno) ";@ ") ivs
    (pp_print_list (pp_print_svi_typed nno) ";@ ") ovs
    (pp_print_list (pp_print_svi_typed nno) ";@ ") lvs
    (pp_print_list (LustreNode.pp_print_node_equation false) "@ ") es
    (pp_print_list (pp_print_svar_instance None) ";@ ") children
    (pp_print_map nno) map

let pp_print_nodes ppf nodes =
  Format.fprintf ppf "@[<v 2>nodes = {@ %a }@]" 
    (pp_print_list pp_print_node ",@ ") nodes

let pp_print_prop ppf prop =
  Format.fprintf ppf
    "@[<v 2>'p%d' : {@ \
      'vars' : [@[<hv>%a@]],@ \
      'expr' : [@[<hv>%a@]] }@]"
    prop.id
    (pp_print_list (pp_print_svi_typed None) ";@ ") prop.vars
    (LustreExpr.pp_print_lustre_expr false) prop.expr

let pp_print_props ppf props =
  (*let rec f i is = if i = List.length props then is else i::(f (i+1) is) in
  let props = List.combine (f 0 []) props in*)
  Format.fprintf ppf "@[<v 2>props = {@ %a }@]" 
    (pp_print_list pp_print_prop ",@ ") props

(* eof *)