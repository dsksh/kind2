open Lib
open LustreNode
open LustreContract

module I = LustreIdent 
module D = LustreIndex
module SV = StateVar
module SVS = StateVar.StateVarSet
module SVT = StateVar.StateVarHashtbl

type svar_instance = SV.t * int list

type node = { 
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
  List.hd(snd name)

let instantiate_svar (nn,id) map sv =
  match SVT.find_opt map sv with
  | Some svi -> svi
  | None -> 
    ( (* Create a local name e.g. Self$id.v. *)  
      let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
      (SV.type_of_state_var sv) in
      sv, id )

let instantiate_svar_trie nn map t =
  D.bindings t |> List.map (fun (_, sv) -> instantiate_svar nn map sv)

let register_arg map (nn, ni) svar0 svar =
  (* Map CN.usr.v to PN$ni.v. *)  
  let n, ty = SV.name_of_state_var svar, SV.type_of_state_var svar in
  let sv = SV.mk_state_var n (SV.scope_of_state_var nn) ty in
  SVT.add map svar0 (sv,ni)

let mk_sv_from_svi ?(is_const:bool = false) (sv,id) =
  let ss = Format.asprintf "%a" ( pp_print_list 
    (fun ppf (s,i) -> Format.fprintf ppf "%s$%d." s i) "" )
    (List.combine (SV.scope_of_state_var sv) id) in
  SV.mk_state_var ~is_const:is_const 
    (ss^(SV.name_of_state_var sv)) [] (SV.type_of_state_var sv)

let mk_subst_sv map sv =
  match SVT.find_opt map sv with
  | Some svi -> mk_sv_from_svi svi
  | None -> sv

let mk_subst_var nno map var =
  let mk_svar map sv =
    match SVT.find_opt map sv with
    | Some svi -> svi
    | None -> ( match nno with
      | Some (nn,id) -> 
        ( (* Create a local name e.g. Self$id.v. *)  
          let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
          (SV.type_of_state_var sv) in
          sv, id )
      | None -> 
          let sv = SV.mk_state_var (SV.name_of_state_var sv) [] (SV.type_of_state_var sv) in
          sv, [] )
  in
  if Var.is_const_state_var var then
    let sv = Var.state_var_of_state_var_instance var in
    (*match SVT.find_opt map sv with
    | Some svi -> Var.mk_const_state_var (mk_sv_from_svi ~is_const:true svi)
    | None -> var*)
    let svi = mk_svar map sv in
    Var.mk_const_state_var (mk_sv_from_svi ~is_const:true svi)
  else if Var.is_state_var_instance var then
    let sv = Var.state_var_of_state_var_instance var in
    (*match SVT.find_opt map sv with
    | Some svi -> let o = Var.offset_of_state_var_instance var in
        Var.mk_state_var_instance (mk_sv_from_svi svi) o
    | None -> var*)
    let svi = mk_svar map sv in
    let o = Var.offset_of_state_var_instance var in
    Var.mk_state_var_instance (mk_sv_from_svi svi) o
  else (* is_free_var *)
    failwith "subst_var w/ free var"

(* *)

let mk_observable node =
  let f ind v (is,os,ls) = let n = SV.name_of_state_var v in
    if String.starts_with ~prefix:"call" n then 
      let n = D.top_max_index is |> succ in (* TODO: adequacy of the index *)
      let is = D.add (D.ListIndex n::ind) v is in
      is, os, ls
    else if not (String.equal "sofar" n) && not (String.starts_with ~prefix:"glocal" n) then
      let n = D.top_max_index os |> succ in (* TODO: index *)
      let os = D.add (D.ListIndex n::ind) v os in
      is, os, ls
    else 
      let n = D.top_max_index ls |> succ in (* TODO: index *)
      let ls = D.add (D.ListIndex n::ind) v ls in
      is, os, ls in
  let ff ls (is,os,l) = 
    let is, os, ls = D.fold f ls (is, os, D.empty) in
    is, os, ls::l in
  let is, os, ls = List.fold_right ff node.locals (node.inputs, node.outputs, []) in
  { node with inputs = is; outputs = os; locals = ls; }

let rec instantiate_node nodes id map node =
  let nm = instantiate_node_name node.LustreNode.name id in
  let cs, id = List.fold_left (instantiate_child nodes nm map) ([],id) node.calls in
  let c_ns = List.map (fun c -> c.name) cs in
  let node = if cs = [] then node else mk_observable node in
  let n = { name = nm; map = map; children = c_ns; src = node } in
  n::cs, id

and instantiate_child nodes p_name map (cs0, id) c =
  let map = SVT.copy map in
  let callee = LustreNode.node_of_name c.call_node_name nodes in
  let _ = List.combine (D.bindings callee.inputs) (D.bindings c.call_inputs) |> 
    List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let _ = List.combine (D.bindings callee.outputs) (D.bindings c.call_outputs) |> 
    List.map (fun ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let cs, id = instantiate_node nodes (id+1) map callee in
  cs0 @ cs, id

let instantiate_main_nodes nodes =
  let map = SVT.create 7 in
  let f (ns,id) n = 
    if n.is_main then instantiate_node nodes (id+1) map n
    else ns, id in
  List.fold_left f ([],0) nodes

let collect_props nn v_map e_map (ps,pids) p =
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

let collect_props_from_contract (ps,cs) ni =
  match ni.src.contract with
  | None -> ps, cs
  | Some c -> 
    let f = collect_props ni.name ni.map ni.src.state_var_expr_map in
    let ps,pids_a = List.fold_left f (ps,[]) c.assumes in
    let gs = fst (List.split c.guarantees) in
    let ps,pids_g = List.fold_left f (ps,[]) gs in 
    let c = id_of_node_instance ni.name, pids_a, pids_g in
    ps, c::cs

let translate_subsystems in_sys =
  let ns = InputSystem.retrieve_lustre_nodes in_sys in
  let nis, _ = instantiate_main_nodes ns in
  let ps, cs = List.fold_left collect_props_from_contract ([],[]) nis in
  (nis, ps, cs)

(* *)

let pp_print_svar_instance nno ppf (sv,id) =
  let b = match nno with
  | Some (nn,id0) ->
    if SV.scope_of_state_var sv <> SV.scope_of_state_var nn || id <> id0 then
      true
    else false
  | None -> true in
  if b then (
    let pr ppf (s,id) = Format.fprintf ppf "%s$%d" s id in
    Format.fprintf ppf "%a."
      (pp_print_list pr ".") (List.combine (SV.scope_of_state_var sv) id) );
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

(* *)

let is_compat_node_pair n1 n2 ps =
  let id1 = id_of_node_instance n1.name in
  let id2 = id_of_node_instance n2.name in
  if id1 < id2 then
    let ovs1 = instantiate_svar_trie n1.name n1.map n1.src.outputs in
    let ovs2 = instantiate_svar_trie n2.name n2.map n2.src.outputs in
    let chk v1 b = b && not (List.mem v1 ovs2) in
    if List.fold_right chk ovs1 true then
      Validator.Compat (id1,id2) :: ps
    else ps
  else ps

let is_compat_node_prop_pair n p ps =
  let id1 = id_of_node_instance n.name in
  let id2 = p.id in
  let ovs1 = instantiate_svar_trie n.name n.map n.src.outputs in
  let ovs2 = p.vars in
  let chk v1 b = b && not (List.mem v1 ovs2) in
  if List.fold_right chk ovs1 true then
    Validator.Compat (id1,-id2) :: ps
  else ps

let is_compat_prop_pair p1 p2 ps =
  if p1.id < p2.id then
    let ovs1 = p1.vars in
    let ovs2 = p2.vars in
    let chk v1 b = b && not (List.mem v1 ovs2) in
    if List.fold_right chk ovs1 true then
      Validator.Compat (-p1.id, -p2.id) :: ps
    else ps
  else ps

let enum_compat_pairs cf np1 l2 ps =
  List.fold_right (cf np1) l2 ps
let enum_compat_pairs cf l1 l2 =
  List.fold_right (fun n -> enum_compat_pairs cf n l2) l1 []

(* *)

let () = 
(* Parse command-line flags. *)
(try
  Flags.parse_argv ()
 with Flags.Error ->
  KEvent.terminate_log () ; exit ExitCodes.error
);

Debug.set_dflags (Flags.debug ()) ;

(* Formatter to write debug output to. *)
(match Flags.debug_log () with
  (* Write to stdout by default. *)
  | None -> ()
  (* Open channel to given file and create formatter on channel. *)
  | Some f ->
    let oc = try open_out f with Sys_error msg ->
      Format.sprintf
        "Could not open debug logfile '%s': '%s'" f msg
      |> failwith
    in
    Debug.set_formatter (Format.formatter_of_out_channel oc)
) ;

let in_file = Flags.input_file () in

KEvent.log L_info "Creating Input system from  %s."
  ( match in_file with
    | "" -> "standard input"
    | _  -> "input file '" ^ in_file ^ "'" );

try
  (*let decls = 
    match LustreInput.ast_of_file in_file with
    | Ok decls -> decls
    | Error e -> LustreReporting.fail_at_position 
        (LustreErrors.error_position e) (LustreErrors.error_message e)
  in
  Format.printf "%a\n" (pp_print_list LustreAst.pp_print_declaration "[end]\n") decls;
  *)

  let input_system = 
    KEvent.log L_debug "Lustre input detected";
    match InputSystem.read_input_lustre (Flags.only_parse ()) in_file with
    | Some in_sys -> in_sys
    | None -> (
        KEvent.log L_note "No parse errors found!";
        KEvent.terminate_log ();
        exit 0 ) in
  KEvent.log L_debug "Input System built";
  Format.printf "%a@." LustreNodePrinter.pp_print_subsystems input_system;
  let ns, ps, cs = translate_subsystems input_system in
  Format.printf "%a@." pp_print_nodes ns;
  Format.printf "%a@." pp_print_props ps;

  (* *)

  let ms = List.map (fun n -> Validator.M (id_of_node_instance n.name)) ns in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") ms;
  (*let ps = List.mapi (fun i p -> p,i+1) ps in*)
  let ms = List.map (fun p -> Validator.M p.id) ps in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") ms;

  let compats = enum_compat_pairs is_compat_node_pair ns ns in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") compats;
  let compats = enum_compat_pairs is_compat_node_prop_pair ns ps in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") compats;
  let compats = enum_compat_pairs is_compat_prop_pair ps ps in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") compats;

  let impls = List.map (fun (mid,ids_a,ids_g) -> Validator.Impl ((mid::ids_a), ids_g)) cs in
  Format.printf "%a@." (pp_print_list Validator.pp_print_constr ",@ ") impls;

  (*Validator.test1 ();*)

  ()
with
(* Could not create input system. *)
| LustreAst.Parser_error  ->
   (* We should have printed the appropriate message so just 'gracefully' exit *)
   KEvent.terminate_log () ; exit ExitCodes.error
| LustreInput.NoMainNode msg ->
   KEvent.log L_fatal "Error reading input file '%s': %s" in_file msg ;
   KEvent.terminate_log () ; exit ExitCodes.error
| Sys_error msg ->
   KEvent.log L_fatal "Error opening input file '%s': %s" in_file msg ;
   KEvent.terminate_log () ; exit ExitCodes.error
| e ->
   let backtrace = Printexc.get_raw_backtrace () in
   KEvent.log L_fatal "Unexpected error:@ %s%a"
     (Printexc.to_string e)
     (if Printexc.backtrace_status ()
      then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
      else fun _ _ -> ()) backtrace;
   (* Terminating log and exiting with error. *)
   KEvent.terminate_log () ;
   exit ExitCodes.error  

(* eof *)