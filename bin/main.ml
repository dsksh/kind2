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
  ivs : svar_instance list;
  ovs : svar_instance list;
  lvs : svar_instance list;
  body : LustreNode.equation list;
  map : svar_instance SVT.t;
  src : LustreNode.t;
}

type prop = {
  (*id : StateVar.t;*)
  map : svar_instance SVT.t;
  expr : LustreExpr.t;
}

let instantiate_node_name name id =
  let s = LustreIdent.string_of_ident false name in
  SV.mk_state_var "node" [s] (Type.mk_int ()), [id]

let instantiate_svar (nn,id) map sv =
  match SVT.find_opt map sv with
  | Some svi -> svi
  | None -> 
    ( (* Create a local name e.g. Self$id.v. *)  
      let sv = SV.mk_state_var (SV.name_of_state_var sv) (SV.scope_of_state_var nn)
      (SV.type_of_state_var sv) in
      sv, id )

(*let translate_node { name; inputs; outputs; locals; equations; _ } =
  let name = instantiate_node_name [] [] 0 name in
  let of_trie t = D.bindings t |> List.split |> snd |> List.map (fun sv -> (sv,[])) in
  let lvs = List.fold_left (fun lvs t -> lvs @ of_trie t) [] locals in
  { name = name; ivs = of_trie inputs; ovs = of_trie outputs; lvs = lvs; body = equations }
*)

(*let translate_subsystems_ (type s) : s InputSystem.t -> node list * prop list =
  (fun in_sys ->
    let lustre_nodes = InputSystem.retrieve_lustre_nodes in_sys in
    let ns = List.map translate_node lustre_nodes in
    let ps = List.fold_left collect_props_from_contract [] lustre_nodes in
    (ns, ps) )
*)

let register_arg map (nn, ni) svar0 svar =
  (* Map CN.usr.v to PN$ni.v. *)  
  let n, ty = SV.name_of_state_var svar, SV.type_of_state_var svar in
  let sv = SV.mk_state_var n (SV.scope_of_state_var nn) ty in
  SVT.add map svar0 (sv,ni)

let instantiate_svar_trie nn map t =
  D.bindings t |> List.map (fun (_, sv) -> instantiate_svar nn map sv)

let instantiate_body id map e =
  (*LustreExpr.map_vars (fun instantiate_svar id map) e*)
  e

let rec instantiate_node nodes id map 
(*{ name; inputs; outputs; locals; calls; equations; _ }*) node =
  (*let ps, ids = match parent with
  | Some (psv, ids) -> (SV.scope_of_state_var psv), ids
  | None -> [], [] in*)
  let name_i = instantiate_node_name node.LustreNode.name id in
  let ivs = instantiate_svar_trie name_i map node.inputs in
  let ovs = instantiate_svar_trie name_i map node.outputs in
  let lvs = List.fold_left 
    (fun lvs l -> lvs @ (instantiate_svar_trie name_i (SVT.create 0) l)) 
    [] node.locals in
  let body = List.map (instantiate_body [id] map) node.equations in
  let n = { name = name_i; ivs = ivs; ovs = ovs; lvs = lvs; body = body; map = map; src = node } in
  let cs, id = List.fold_left (instantiate_child nodes name_i map) ([],id) node.calls in
  n::cs, id

and instantiate_child nodes p_name map (cs0, id) c =
  let map = SVT.copy map in
  let callee = LustreNode.node_of_name c.call_node_name nodes in
  let _ = List.combine (D.bindings callee.inputs) (D.bindings c.call_inputs) |> 
    List.mapi (fun i ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let _ = List.combine (D.bindings callee.outputs) (D.bindings c.call_outputs) |> 
    List.mapi (fun i ((_,sv0), (_,sv1)) -> register_arg map p_name sv0 sv1) in
  let cs, id = instantiate_node nodes (id+1) map callee in
  cs0 @ cs, id

let instantiate_main_nodes nodes =
  let map = SVT.create 7 in
  let f (ns,id) n = 
    if n.is_main then instantiate_node nodes (id+1) map n
    else ns, id in
  List.fold_left f ([],0) nodes

let collect_props nn v_map0 e_map ps p =
  let e = match SVT.find_opt e_map p.svar with
  | Some e -> e 
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  let svs = LustreExpr.state_vars_of_expr e in
  let v_map = SVT.create (SVS.cardinal svs) in
  let f sv = SVT.add v_map sv (instantiate_svar nn v_map0 sv) in
  let _ = SVS.iter f svs in
  let eq_entry (k1,(v1,i1)) (k2,(v2,i2)) = (k1 = k2 && v1 = v2 && i1 = i2) in
  let eq_map m1 m2 = Seq.equal eq_entry (SVT.to_seq m1) (SVT.to_seq m2) in
  match List.find_opt (fun p -> eq_map p.map v_map && p.expr = e) ps with
  | Some _ -> ps
  | None ->
    (*let vs = LustreExpr.state_vars_of_expr e in*)
    let p = { map = v_map; expr = e } in
    p::ps

let collect_props_from_contract ps ni =
  match ni.src.contract with
  | None -> ps
  | Some c -> 
    let ps = List.fold_left (collect_props ni.name ni.map ni.src.state_var_expr_map) ps c.assumes in
    let gs = fst (List.split c.guarantees) in
    let ps = List.fold_left (collect_props ni.name ni.map ni.src.state_var_expr_map) ps gs in 
    ps

let translate_subsystems in_sys =
  let ns = InputSystem.retrieve_lustre_nodes in_sys in
  let nis, _ = instantiate_main_nodes ns in
  let ps = List.fold_left collect_props_from_contract [] nis in
  (nis, ps)

(* *)

let pp_print_svar_instance nn ppf (sv,id) =
  let b = match nn with
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

(*let pp_print_svar ppf (_, sv) =*)
let pp_print_svi_typed nn ppf sv =
  Format.fprintf ppf
    "('%a', '%a')"
    (pp_print_svar_instance nn) sv
    Type.pp_print_type (SV.type_of_state_var (fst sv))

(*let pp_print_svar_trie ppf t = 
  D.bindings t |> pp_print_list (fun ppf (_, sv) -> pp_print_svar ppf sv) ";@ " ppf*)

let pp_print_map nn ppf map =
  SVT.iter 
    ( fun v0 v1 -> Format.fprintf ppf "@[<hv 2>%s =@ %a;@ @]"
      (SV.name_of_state_var v0)
      (pp_print_svar_instance nn) v1 )
    map

let pp_print_node ppf node =
  let nn = Some node.name in
  Format.fprintf ppf
  "'%a' : @[<hv 2>\
      { 'ivs' : [@[<hv>%a@]],@ \
        'ovs' : [@[<hv>%a@]],@ \
        'lvs' : [@[<hv>%a@]],@ \
        'body' : [@[<hv>%a@]],@ \
        'map' : [@[<hv>%a@]]}@]"
    (*(I.pp_print_ident false) node.name*)
    (pp_print_svar_instance None) node.name
    (pp_print_list (pp_print_svi_typed nn) ";@ ") node.ivs
    (pp_print_list (pp_print_svi_typed nn) ";@ ") node.ovs
    (pp_print_list (pp_print_svi_typed nn) ";@ ") node.lvs
    (*(pp_print_list pp_print_svar_trie ";@ ") node.lvs*)
    (pp_print_list (LustreNode.pp_print_node_equation false) "@ ") node.body
    (pp_print_map nn) node.map

let pp_print_nodes ppf nodes =
  Format.fprintf ppf "nodes = @ \
  @[<hv 2>{%a}@]" (pp_print_list pp_print_node ",@ ") nodes

let pp_print_prop ppf (i, prop) =
  Format.fprintf ppf
  "'p%d' : @[<hv 2>\
      { 'vars' : [@[<hv>%a@]],@ \
        'expr' : [@[<hv>%a@]],@ \
        'map' : [@[<hv>%a@]]}@]"
    i
    (*(fun ppf -> SVS.iter (SV.pp_print_state_var ppf)) prop.vars*)
    (fun ppf -> Seq.iter (pp_print_svar_instance None ppf)) (SVT.to_seq_values prop.map)
    (LustreExpr.pp_print_lustre_expr false) prop.expr
    (pp_print_map None) prop.map

let pp_print_props ppf props =
  let rec f i is = if i = List.length props then is else i::(f (i+1) is) in
  let props = List.combine (f 0 []) props in
  Format.fprintf ppf "props = @ \
  @[<hv 2>{%a}@]" (pp_print_list pp_print_prop ",@ ") props

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
        exit 0
    ) 
  in
  KEvent.log L_debug "Input System built";
  (*Format.printf "%a\n" InputSystem.pp_print_subsystems_debug input_system*)
  (*Format.printf "%a\n" InputSystem.pp_print_state_var_instances_debug input_system;*)
  Format.printf "%a\n" LustreNodePrinter.pp_print_subsystems input_system;
  (*let param = InputSystem.interpreter_param input_system in*)
  (*let param = List.hd (InputSystem.mcs_params input_system) in*)
  (*let sys, _ = InputSystem.trans_sys_of_analysis ~preserve_sig:false ~slice_nodes:true input_system param in*)
  (*Format.printf "%a\n" TransSys.pp_print_trans_sys sys*)
  (*let in_sys = InputSystem.slice_to_abstraction input_system param sys in
  Format.printf "%a\n" pp_print_subsystems in_sys;*)

  let (ns, ps) = translate_subsystems input_system in
  Format.printf "%a\n" pp_print_nodes ns;
  Format.printf "%a\n" pp_print_props ps
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
   KEvent.log L_fatal "Error opening input file '%s':@ %s%a"
     (in_file) (Printexc.to_string e)
     (if Printexc.backtrace_status ()
      then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
      else fun _ _ -> ()) backtrace;
   (* Terminating log and exiting with error. *)
   KEvent.terminate_log () ;
   exit ExitCodes.error  
