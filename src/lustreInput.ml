(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib

module A = LustreAst
module I = LustreIdent
module N = LustreNode
module C = LustreContext
module D = LustreDeclarations


(* Parse from input channel *)
let of_channel keep_all_coi in_ch = 

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (Flags.input_file ())
     with Failure _ -> Sys.getcwd ());

  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 

      | LustreParser.Error ->

        let lexer_pos = 
          Lexing.lexeme_start_p lexbuf 
        in

        C.fail_at_position
          (position_of_lexing lexer_pos)
          "Syntax error"

  in

  (* Simplify declarations to a list of nodes *)
  let nodes = D.declarations_to_nodes declarations in
  
  (* Find main node by annotation *)
  let main_node = 

    match Flags.lustre_main () with 

      | None -> 

        (try 
          
          LustreNode.find_main nodes 
            
        with Not_found -> 
          
          raise (Invalid_argument "No main node defined in input"))

      | Some s -> LustreIdent.mk_string_ident s

  in

  Format.printf 
    "@[<v>Before slicing@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes;

  let nodes_impl = LustreSlicing.slice_to_impl nodes in

  Format.printf 
    "@[<v>After slicing to implementation@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_impl;

  let nodes_contract = LustreSlicing.slice_to_contract nodes in

  Format.printf 
    "@[<v>After slicing to contract@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_contract;

  (* LustreTransSys.trans_sys_of_nodes nodes_contract nodes_impl *)
  ()


(*

  (* Consider only nodes called by main node *)
  let nodes_coi = 
    if keep_all_coi then 
      LustreSlicing.reduce_wo_coi (List.rev nodes) main_node
    else
      LustreNode.reduce_to_props_coi (List.rev nodes) main_node
  in

  debug lustreInput
    "@[<v>After slicing@,%a@]"
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_coi
  in
*)
(*
  (* Create transition system of Lustre nodes *)
  let fun_defs_init, fun_defs_trans, state_vars, init, trans, props = 
    LustreTransSys.trans_sys_of_nodes main_node nodes_coi
  in

  (* Extract properties from nodes *)
  let props = 
    LustreTransSys.props_of_nodes main_node nodes_coi
  in

  let trans_sys = 
 (* Create Kind transition system *)
    TransSys.mk_trans_sys 
      (List.combine fun_defs_init fun_defs_trans)
      state_vars
      init
      trans
      props
      (TransSys.Lustre nodes_coi)
  in
  *)
(*
  let trans_sys =
    LustreTransSys.trans_sys_of_nodes nodes_coi
  in

  (debug lustreInput 
      "%a"
      TransSys.pp_print_trans_sys trans_sys
   in

   Event.log
     L_info
     "Lustre main node is %a"
     (I.pp_print_ident false) main_node;
*)
(*
  Format.printf 
    "%a@."
    (pp_print_list 
       (fun ppf state_var -> 
          Format.fprintf ppf "%a=%a"
            StateVar.pp_print_state_var state_var
            LustreExpr.pp_print_state_var_source 
            (LustreExpr.get_state_var_source state_var))
       ",@ ")
    state_vars);
  trans_sys)

*)

(* Open and parse from file *)
let of_file keep_all_coi filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel keep_all_coi in_ch

;;

of_file false Sys.argv.(1)



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
