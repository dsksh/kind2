open Lib
open LustreNode
open LustreContract

module I = LustreIdent 
module D = LustreIndex
module SV = StateVar
module SVS = StateVar.StateVarSet
module SVT = StateVar.StateVarHashtbl

type svar_instance = SV.t * int list

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
  SV.mk_state_var "node" [s] (Type.mk_int ()), [id]

let id_of_node_instance name =
  List.hd (snd name)

let hd_of_scope sv = 
  match SV.scope_of_state_var sv with
  | s::_ -> s
  | [] -> ""

let pp_print_scope_hd ppf (sv,id) =
  match SV.scope_of_state_var sv with
  | s::_ -> 
    Format.fprintf ppf "%s_%a__" s
      (pp_print_list Format.pp_print_int ",") id 
  | [] -> ()

let instantiate_svar (nn,id) map sv =
  match SVT.find_opt map sv with
  | Some svi -> svi
  | None -> 
    ( (* Create a local name e.g. Self___id__v. *)  
      let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
      (SV.type_of_state_var sv) in
      sv, id )

let instantiate_svar_trie nn map t =
  D.bindings t |> List.map (fun (_, sv) -> instantiate_svar nn map sv)

let register_arg map (nn, ni) svar0 svar =
  (* Map CN.usr.v to PN___ni__v. *)  
  (*let n, ty = SV.name_of_state_var svar, SV.type_of_state_var svar in
  let sv = SV.mk_state_var n (SV.scope_of_state_var nn) ty in
  SVT.add map svar0 (sv,ni)*)
  SVT.add map svar0 (svar,ni);
  (* TODO: redundant entry for nested calls. *)
  let svar0_embedded = 
    SV.mk_state_var (SV.name_of_state_var svar0) [] (SV.type_of_state_var svar0) in
  SVT.add map svar0_embedded (svar,ni)

let mk_sv_from_svi ?(is_const:bool = false) (sv,id) =
  (*Format.printf "msfs %a %a@." SV.pp_print_state_var sv (pp_print_list Format.pp_print_int ",") id;*)
  (*let ss = Format.asprintf "%a" ( pp_print_list 
    (fun ppf (s,i) -> Format.fprintf ppf "%s___%d__" s i) "" )
    (List.combine (SV.scope_of_state_var sv) id) in*)
  let ss = Format.asprintf "%a" pp_print_scope_hd (sv,id)
  in
  SV.mk_state_var ~is_const:is_const 
    (ss^(SV.name_of_state_var sv)) [] (SV.type_of_state_var sv)

let mk_subst_sv map sv =
  match SVT.find_opt map sv with
  | Some svi -> mk_sv_from_svi svi
  | None -> sv

let mk_subst_var ?(inherited = None) nno map var =
  let mk_svar sv =
    let () = Format.printf "%a: " StateVar.pp_print_state_var sv in
    match SVT.find_opt map sv with
    | Some (sv,id) -> ( 
        Format.printf "%a is found@." StateVar.pp_print_state_var sv;
        match inherited with
        | Some sc -> 
          (* Case of getting a property inherited from a child instance (who manages the map) to 
             a parent instance (inherited). Omit printing the scope. *)
          (*if SV.scope_of_state_var sv = sc then*)
          if List.length sc > 0 && List.hd sc = hd_of_scope sv then
            let sv = SV.mk_state_var (SV.name_of_state_var sv) [] (SV.type_of_state_var sv) in
            sv, []
          else (sv,id)
        | None -> (sv,id) 
      )
    | None -> ( 
        Format.printf "not found@.";
        match nno with
        | Some (nn,id) -> 
          ( (* Create a local name e.g. Self___id.v. *)  
            let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
            (SV.type_of_state_var sv) in
            sv, id )
        | None -> 
            let sv = SV.mk_state_var (SV.name_of_state_var sv) [] (SV.type_of_state_var sv) in
            sv, [] 
      )
  in
  if Var.is_const_state_var var then
    let sv = Var.state_var_of_state_var_instance var in
    let svi = mk_svar sv in
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

let add_ghost_vs node =
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

(*let transfer_contracts nodes node =
  let f call (ass,gs) =
    let callee = LustreNode.node_of_name call.call_node_name nodes in
    match callee.contract with
    | None -> ass, gs
    | Some c -> 
      let ass = ass @ fst (List.split c.guarantees) in
      let gs = gs @ (List.map (fun sv -> sv, true) c.assumes) in (* TODO *)
      ass, gs
  in
  let (ass,gs) = List.fold_right f node.calls ([],[]) in
  let contract = match node.contract with
  | None -> 
    let sv = SV.mk_state_var "sofar" [] Type.t_bool in (* TODO *)
    Some { assumes = ass; guarantees = gs; sofar_assump = sv; modes = [] }
  | Some c -> 
    Some ({ c with assumes = c.assumes @ ass; guarantees = c.guarantees @ gs }) in
  { node with contract = contract }
*)

(* *)

(* Make some local variables observable (as input or output variables). *)
let mk_observable node =
  let f _ v (is,os,ls) = let n = SV.name_of_state_var v in
    (*Format.printf "%a@." (pp_print_list (D.pp_print_one_index false) ",") ind;*)
    if String.starts_with ~prefix:"call" n then 
      add_sv_to_trie v is, os, ls
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

let rec instantiate_node nodes id map node =
  let nm = instantiate_node_name node.LustreNode.name id in
  (*Format.printf "instantiate %a@." (LustreIdent.pp_print_ident true) node.name;*)
  let cs, cs_all, id = List.fold_right (instantiate_child nodes nm map) node.calls ([],[],id) in
  let c_ns = List.map (fun c -> c.name) cs in
  let node = if cs = [] then node else mk_observable node in
  let n = { name = nm; map = map; children = c_ns; src = node } in
  n, cs @ cs_all, id

and instantiate_child nodes p_name map c (cs0, cs_all0, id) =
  (* A binding map. *)
  let map = SVT.copy map in
  (* Obtain the child node entry. *)
  let callee = LustreNode.node_of_name c.call_node_name nodes in
  (* Prepare the binding map. *)
  let _ = List.combine (D.bindings callee.inputs) (D.bindings c.call_inputs) |> 
    List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let _ = List.combine (D.bindings callee.outputs) (D.bindings c.call_outputs) |> 
    List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let ci, cs, id = instantiate_node nodes (id+1) map callee in
  cs0 @ [ci], cs @ cs_all0, id

let instantiate_main_nodes nodes =
  let map = SVT.create 7 in
  let f n (ns,id) = 
    if n.is_main then 
      let n, cs, id = instantiate_node nodes (id+1) map n in 
      n::cs, id
    else ns, id in
  List.fold_right f nodes ([],0)

let collect_props nn v_map e_map p (ps,pids) =
  let e0 = match SVT.find_opt e_map p.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  let svs = LustreExpr.state_vars_of_expr e0 in
  let svis = SVS.fold (fun sv l -> (instantiate_svar nn v_map sv)::l) svs [] in
  let expr = LustreExpr.map_vars (mk_subst_var (Some nn) v_map) e0 in
  match List.find_opt (fun p -> LustreExpr.equal p.expr expr) ps with
  | Some p -> ps, List.sort (fun i j -> -(Int.compare i j)) (p.id::pids)
  | None -> 
      let id = -1 - (List.length ps) in
      ps @ [{ id = id; vars = svis; expr = expr }], pids @ [id]

let collect_props_from_contract ni (ps,cs,goals) =
  match ni.src.contract with
  | None -> ps, cs, goals
  | Some c -> 
    let f = collect_props ni.name ni.map ni.src.state_var_expr_map in
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