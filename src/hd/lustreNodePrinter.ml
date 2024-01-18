open Lib
open LustreNode

(* Module abbreviations *)
module I = LustreIdent 
module D = LustreIndex
module E = LustreExpr
module C = LustreContract

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl

let pp_print_node ppf 
    { name;
      (*is_extern;*)
      instance;
      init_flag;
      inputs; 
      oracles; 
      outputs; 
      locals; 
      equations; 
      calls; 
      asserts; 
      props;
      contract;
      is_main;
      is_function;
      state_var_source_map;
      oracle_state_var_map;
      state_var_expr_map; 
      _ (* assumption_svars *) } = 

  let pp_print_equation = LustreNode.pp_print_node_equation false in

  let pp_print_prop ppf (state_var, name, source) = 
    Format.fprintf
      ppf
      "%a (%s, %a)"
      StateVar.pp_print_state_var state_var
      name
      Property.pp_print_prop_source source
  in

  let pp_print_state_var_source ppf = 
    let p sv src = Format.fprintf ppf "%a:%s" StateVar.pp_print_state_var sv src in
    function 
      | (sv, LustreNode.Input) -> p sv "in"
      | (sv, LustreNode.Output) -> p sv "out"
      | (sv, LustreNode.Local) -> p sv "loc"
      | (sv, LustreNode.KLocal) -> p sv "k-loc"
      | (sv, LustreNode.Call) -> p sv "cl"
      | (sv, LustreNode.Ghost) -> p sv "gh"
      | (sv, LustreNode.KGhost) -> p sv "k-gh"
      | (sv, LustreNode.Oracle) -> p sv "or"
      (* | (sv, Alias (sub, _)) -> p sv (
        Format.asprintf "al(%a)"
          StateVar.pp_print_state_var sub
      )*)
  in

  let pp_print_oracle_state_var_map =
    pp_print_pair
      StateVar.pp_print_state_var
      StateVar.pp_print_state_var
      ":"
  in

  let pp_print_state_var_expr_map =
    pp_print_pair
      StateVar.pp_print_state_var
      (LustreExpr.pp_print_lustre_expr true)
      ":"
  in

  let pp_print_state_var_as_tuple ppf sv =
    Format.fprintf ppf
      "('%s', '%a')"
      (*(StateVar.string_of_state_var sv.Hashcons.node)*)
      (StateVar.string_of_state_var sv)
      Type.pp_print_type (StateVar.type_of_state_var sv)
      (*Type.pp_print_type sv.Hashcons.prop.StateVar.var_type*)
  in

  let pp_print_state_var_trie_debug ppf t = 
    D.bindings t |> 
    pp_print_list
      (fun ppf (_, sv) -> 
         (*if i = D.empty_index then 
           (*StateVar.pp_print_state_var ppf sv*)
           pp_print_state_var_as_tuple ppf sv
         else
           Format.fprintf 
             ppf
             "%a: %a"
             (D.pp_print_index false) i
             StateVar.pp_print_state_var sv)*)
         pp_print_state_var_as_tuple ppf sv)
      ";@ "
      ppf
  in

  let pp_print_cond ppf = function
    (* | CNone -> Format.pp_print_string ppf "None" *)
    | CActivate c ->
      Format.fprintf ppf "activate on %a" StateVar.pp_print_state_var c
    | CRestart r ->
      Format.fprintf ppf "restart on %a" StateVar.pp_print_state_var r
  in

  let pp_print_conds ppf = pp_print_list pp_print_cond ",@ " ppf in

  let pp_print_node_call_debug 
      ppf
      { 
        call_pos;
        call_node_name; 
        call_cond; 
        call_inputs; 
        call_oracles; 
        call_outputs;
        _ (* call_defaults *) } =

    Format.fprintf
      ppf
      "call %a { @[<hv>pos      = %a;@ \
                       cond     = %a;@ \
                       inputs   = [@[<hv>%a@]];@ \
                       oracles  = [@[<hv>%a@]];@ \
                       outputs  = [@[<hv>%a@]]; }@]"
      (I.pp_print_ident false) call_node_name
      pp_print_position call_pos
      pp_print_conds call_cond
      pp_print_state_var_trie_debug call_inputs
      (pp_print_list StateVar.pp_print_state_var ";@ ") call_oracles
      pp_print_state_var_trie_debug call_outputs
  in

  Format.fprintf 
    ppf
    "node %a @[<hv 2>\
       { instance =  %a;@ \
         init_flag = %a;@ \
         inputs =     [@[<hv>%a@]];@ \
         oracles =    [@[<hv>%a@]];@ \
         outputs =    [@[<hv>%a@]];@ \
         locals =     [@[<hv>%a@]];@ \
         equations =  [@[<hv>%a@]];@ \
         calls =      [@[<hv>%a@]];@ \
         asserts =    [@[<hv>%a@]];@ \
         props =      [@[<hv>%a@]];@ \
         contract =   [@[<hv>%a@]];@ \
         is_main =    @[<hv>%B@];@ \
         is_function =    @[<hv>%B@];@ \
         state_var_source_map = [@[<hv>%a@]];@ \
         oracle_state_var_map = [@[<hv>%a@]];@ \
         state_var_expr_map = [@[<hv>%a@]]; }@]"

    (I.pp_print_ident false) name
    StateVar.pp_print_state_var instance
    StateVar.pp_print_state_var init_flag
    pp_print_state_var_trie_debug inputs
    (pp_print_list StateVar.pp_print_state_var ";@ ") oracles
    pp_print_state_var_trie_debug outputs
    (pp_print_list pp_print_state_var_trie_debug ";@ ") locals
    (pp_print_list pp_print_equation "@ ") equations
    (pp_print_list pp_print_node_call_debug ";@ ") calls
    (pp_print_list (fun fmt (_,sv) -> E.pp_print_lustre_var false fmt sv) ";@ ") asserts
    (pp_print_list pp_print_prop ";@ ") props
    (fun fmt -> function
      | None -> ()
      | Some contract ->
        Format.fprintf fmt "%a@ "
          (C.pp_print_contract_debug false) contract) contract
    is_main
    is_function
    (pp_print_list pp_print_state_var_source ";@ ")
      (SVM.bindings state_var_source_map)
    (pp_print_list pp_print_oracle_state_var_map ";@")
      (SVT.fold (fun k v acc -> (k, v) :: acc) oracle_state_var_map [])
    (pp_print_list pp_print_state_var_expr_map ";@")
      (SVT.fold (fun k v acc -> (k, v) :: acc) state_var_expr_map [])

let pp_print_subsystems (type s) : Format.formatter -> s InputSystem.t -> unit =
  (fun fmt in_sys ->
    let lustre_nodes = InputSystem.retrieve_lustre_nodes in_sys in
    List.iter (Format.fprintf fmt "%a@." pp_print_node) lustre_nodes
  )

(* eof *)