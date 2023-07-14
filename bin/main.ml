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
  (*ivs : svar_instance list;
  ovs : svar_instance list;
  lvs : svar_instance list;
  body : LustreNode.equation list;*)
  map : svar_instance SVT.t;
  children : svar_instance list;
  src : LustreNode.t;
}

type prop = {
  vars : svar_instance list;
  expr : LustreExpr.t;
}

(* *)

let mk_sv_from_svi ?(is_const:bool = false) (sv,id) =
  let ss = Format.asprintf "%a" ( pp_print_list 
    (fun ppf (s,i) -> Format.fprintf ppf "%s$%d" s i) "." )
    (List.combine (SV.scope_of_state_var sv) id) in
  SV.mk_state_var ~is_const:is_const 
    (ss^"."^(SV.name_of_state_var sv)) [] (SV.type_of_state_var sv)

let mk_subst_sv map sv =
  match SVT.find_opt map sv with
  | Some svi -> mk_sv_from_svi svi
  | None -> sv

let mk_subst_var map var =
  if Var.is_const_state_var var then
    let sv = Var.state_var_of_state_var_instance var in
    match SVT.find_opt map sv with
    | Some svi -> Var.mk_const_state_var (mk_sv_from_svi ~is_const:true svi)
    | None -> var
  else if Var.is_state_var_instance var then
    let sv = Var.state_var_of_state_var_instance var in
    match SVT.find_opt map sv with
    | Some svi -> let o = Var.offset_of_state_var_instance var in
        Var.mk_state_var_instance (mk_sv_from_svi svi) o
    | None -> var
  else (* is_free_var *)
    failwith "subst_var w/ free var"

(* *)

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

let instantiate_svar_trie nn map t =
  D.bindings t |> List.map (fun (_, sv) -> instantiate_svar nn map sv)

let register_arg map (nn, ni) svar0 svar =
  (* Map CN.usr.v to PN$ni.v. *)  
  let n, ty = SV.name_of_state_var svar, SV.type_of_state_var svar in
  let sv = SV.mk_state_var n (SV.scope_of_state_var nn) ty in
  SVT.add map svar0 (sv,ni)

(*let instantiate_body id map e =
  (*LustreExpr.map_vars (fun instantiate_svar id map) e*)
  e
*)

let rec instantiate_node nodes id map node =
  let nm = instantiate_node_name node.LustreNode.name id in
  let cs, id = List.fold_left (instantiate_child nodes nm map) ([],id) node.calls in
  let c_ns = List.map (fun c -> c.name) cs in
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

let collect_props nn v_map e_map ps p =
  let e0 = match SVT.find_opt e_map p.svar with
  | Some e -> e
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  in
  let svs = LustreExpr.state_vars_of_expr e0 in
  (*let svis = SVS.fold ( fun sv l -> match (SVT.find_opt v_map sv) with
  | Some svi -> svi::l
  | None -> failwith (Format.asprintf "%a" SV.pp_print_state_var sv) ) svs [] in*)
  let svis = SVS.fold (fun sv l -> (instantiate_svar nn v_map sv)::l) svs [] in
  let expr = LustreExpr.map_vars (mk_subst_var v_map) e0 in
  match List.find_opt (fun p -> p.expr = expr) ps with
  | Some _ -> ps 
  | None -> 
      ps @ [{ vars = svis; expr = expr }]

let collect_props_from_contract ps ni =
  match ni.src.contract with
  | None -> ps
  | Some c -> 
    let ps = List.fold_left 
      (collect_props ni.name ni.map ni.src.state_var_expr_map) ps c.assumes in
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

let pp_print_svi_typed nn ppf sv =
  Format.fprintf ppf
    "('%a', '%a')"
    (pp_print_svar_instance nn) sv
    Type.pp_print_type (SV.type_of_state_var (fst sv))

let pp_print_map nn ppf map =
  SVT.iter 
    ( fun v0 v1 -> Format.fprintf ppf "@[<hv 2>%s =@ %a;@ @]"
      (SV.name_of_state_var v0)
      (pp_print_svar_instance nn) v1 )
    map

let pp_print_node ppf { name; map; children; src } =
  let nn = Some name in
  let ivs = instantiate_svar_trie name map src.inputs in
  let ovs = instantiate_svar_trie name map src.inputs in
  let lvs = List.fold_left 
    (fun lvs l -> lvs @ (instantiate_svar_trie name (SVT.create 0) l)) 
    [] src.locals in
  let es = List.map ( fun ((v,bf),body) -> 
      (mk_subst_sv map v, bf), LustreExpr.map_vars (mk_subst_var map) body )
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
    (pp_print_list (pp_print_svi_typed nn) ";@ ") ivs
    (pp_print_list (pp_print_svi_typed nn) ";@ ") ovs
    (pp_print_list (pp_print_svi_typed nn) ";@ ") lvs
    (pp_print_list (LustreNode.pp_print_node_equation false) "@ ") es
    (pp_print_list (pp_print_svar_instance None) ";@ ") children
    (pp_print_map nn) map

let pp_print_nodes ppf nodes =
  Format.fprintf ppf "@[<hv 2>nodes = {@ %a }@]" 
    (pp_print_list pp_print_node ",@ ") nodes

let pp_print_prop ppf (i, prop) =
  (*let expr = LustreExpr.map_vars (mk_subst_var prop.map) prop.expr in*)
  Format.fprintf ppf
    "@[<v 2>'p%d' : {@ \
      'vars' : [@[<hv>%a@]],@ \
      'expr' : [@[<hv>%a@]] }@]"
    i
    (*(fun ppf -> Seq.iter (pp_print_svar_instance None ppf)) (SVT.to_seq_values prop.map)*)
    (pp_print_list (pp_print_svi_typed None) ";@ ") prop.vars
    (LustreExpr.pp_print_lustre_expr false) prop.expr
    (*(pp_print_map None) prop.map*)

let pp_print_props ppf props =
  let rec f i is = if i = List.length props then is else i::(f (i+1) is) in
  let props = List.combine (f 0 []) props in
  Format.fprintf ppf "@[<v 2>props = {@ %a }@]" 
    (pp_print_list pp_print_prop ",@ ") props

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
  Format.printf "%a\n" LustreNodePrinter.pp_print_subsystems input_system;
  let ns, ps = translate_subsystems input_system in
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
   KEvent.log L_fatal "Unexpected error:@ %s%a"
     (Printexc.to_string e)
     (if Printexc.backtrace_status ()
      then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
      else fun _ _ -> ()) backtrace;
   (* Terminating log and exiting with error. *)
   KEvent.terminate_log () ;
   exit ExitCodes.error  

(* eof *)