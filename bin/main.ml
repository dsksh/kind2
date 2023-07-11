open Lib
open LustreNode
open LustreContract
(*open LustreAst
open LustreNodePrinter
open LustreAstPrinter*)

module I = LustreIdent 
module D = LustreIndex
module SVS = StateVar.StateVarSet
module SVT = StateVar.StateVarHashtbl

(*
type t =
  | Node of { 
    name : LustreAst.ident;  
    ivs : (LustreAst.ident * LustreAst.lustre_type) list;
    ovs : (LustreAst.ident * LustreAst.lustre_type) list;
    body : LustreAst.node_item list;
  }
  | Prop of {
    name : LustreAst.ident;
    vars : LustreAst.ident list;
    expr : LustreAst.expr;
  }

let node_of_decl (n, ext, p, i, o, l, e, r) =
  let ivs = List.map (fun (_, s, t, _, _) -> (s, t)) i in
  let ovs = List.map (fun (_, s, t, _) -> (s, t)) o in
  { name = n; ivs = ivs; ovs = ovs; body = e }

let node_of_ast = function
  | NodeDecl (span, decl) ->
    Some (node_of_decl decl)
  | _ -> None
*)

type node = { 
  name : I.t;  
  ivs : StateVar.t D.t;
  ovs : StateVar.t D.t;
  lvs : StateVar.t D.t list;
  body : LustreNode.equation list;
}

type prop = {
  (*id : StateVar.t;*)
  vars : SVS.t;
  expr : LustreExpr.t;
}

(*let translate_node (n : LustreNode.t) =
  { name = n.name; ivs = n.inputs; ovs = n.outputs; lvs = n.locals; body = n.equations }*)
let translate_node { name; inputs; outputs; locals; equations; _ } =
  { name = name; ivs = inputs; ovs = outputs; lvs = locals; body = equations }

let collect_props map ps p =
  let e = match SVT.find_opt map p.svar with
  | None -> failwith (Format.asprintf "no expr for %a" LustreContract.pp_print_svar p)
  | Some e -> e 
  in
  match List.find_opt (fun p -> p.expr = e) ps with
  | Some _ -> ps
  | None ->
    let vs = LustreExpr.state_vars_of_expr e in
    let p = { vars = vs; expr = e } in
    p::ps

let collect_props_from_contract ps node =
  match node.contract with
  | None -> ps
  | Some c -> 
    let ps = List.fold_left (collect_props node.state_var_expr_map) ps c.assumes in
    let gs = fst (List.split c.guarantees) in
    let ps = List.fold_left (collect_props node.state_var_expr_map) ps gs in 
    ps

let translate_subsystems (type s) : s InputSystem.t -> node list * prop list =
  (fun in_sys ->
    let lustre_nodes = InputSystem.retrieve_lustre_nodes in_sys in
    let ns = List.map translate_node lustre_nodes in
    let ps = List.fold_left collect_props_from_contract [] lustre_nodes in
    (ns, ps) )

(* *)

(*let pp_print_svar ppf (_, sv) =*)
let pp_print_svar ppf sv =
  Format.fprintf ppf
    "('%s', '%a')"
    (StateVar.string_of_state_var sv)
    Type.pp_print_type (StateVar.type_of_state_var sv)

let pp_print_svar_trie ppf t = 
  D.bindings t |> pp_print_list (fun ppf (_, sv) -> pp_print_svar ppf sv) ";@ " ppf

let pp_print_node ppf node =
  Format.fprintf ppf
  "'%a' : @[<hv>\
      { 'ivs' : [@[<hv>%a@]],@ \
        'ovs' : [@[<hv>%a@]],@ \
        'lvs' : [@[<hv>%a@]],@ \
        'body' : [@[<hv>%a@]]}@]"
    (I.pp_print_ident false) node.name
    pp_print_svar_trie node.ivs
    pp_print_svar_trie node.ovs
    (pp_print_list pp_print_svar_trie ";@ ") node.lvs
    (pp_print_list (LustreNode.pp_print_node_equation false) "@ ") node.body

let pp_print_nodes ppf nodes =
  Format.fprintf ppf "nodes = @ \
  @[<hv 2>{%a}@]" (pp_print_list pp_print_node ",@ ") nodes

let pp_print_prop ppf (i, prop) =
  Format.fprintf ppf
  "'p%d' : @[<hv>\
      { 'vars' : [@[<hv>%a@]],@ \
        'expr' : [@[<hv>%a@]]}@]"
    i
    (fun ppf -> SVS.iter (pp_print_svar ppf)) prop.vars
    (LustreExpr.pp_print_lustre_expr false) prop.expr

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
  let decls = 
    match LustreInput.ast_of_file in_file with
    | Ok decls -> decls
    | Error e -> LustreReporting.fail_at_position 
        (LustreErrors.error_position e) (LustreErrors.error_message e)
  in
  Format.printf "%a\n" (pp_print_list LustreAst.pp_print_declaration "[end]\n") decls;

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
