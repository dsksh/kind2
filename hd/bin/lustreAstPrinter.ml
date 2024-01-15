open Lib
open LustreAst

let pp_print_contract_ghost_const ppf = function 

  | FreeConst (_, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (_, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (_, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_ghost_var ppf = function 

  | FreeConst (_, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (_, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (_, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_assume ppf (_, n, s, e) =
  Format.fprintf
    ppf
    "@[<hv 3>%sassume%s@ %a;@]"
    (if s then "weakly " else "")
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

let pp_print_contract_guarantee ppf (_, n, s, e) =
  Format.fprintf
    ppf
    "@[<hv 3>%sguarantee%s@ %a;@]"
    (if s then "weakly " else "")
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

    
let pp_print_contract_require ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>require%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

let pp_print_contract_ensure ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>ensure%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

let cond_new_line b fmt () =
  if b then Format.fprintf fmt "@ " else Format.fprintf fmt ""

let pp_print_contract_mode ppf (_, id, reqs, enss) =
  Format.fprintf
    ppf
    "@[<hv 2>mode %a (%a%a%a%a@]%a) ;"
    pp_print_ident id
    (cond_new_line (reqs <> [])) ()
    (pp_print_list pp_print_contract_require "@ ") reqs
    (cond_new_line (enss <> [])) ()
    (pp_print_list pp_print_contract_ensure "@ ") enss
    (cond_new_line ((reqs,enss) <> ([],[]))) ()

let pp_print_contract_call fmt (_, id, in_params, out_params) =
  Format.fprintf
    fmt "@[<hov 2>import %a (@,%a@,) returns (@,%a@,) ;@]"
    pp_print_ident id
    (pp_print_list pp_print_expr ", ") in_params
    (pp_print_list pp_print_ident ", ") out_params

let pp_print_contract_assump_vars fmt (_, vars) =
  Format.fprintf
    fmt "@[<hov 2>assumption_vars %a ;@]"
    (pp_print_list pp_print_ident ", ")
    (List.map (fun (_,v) -> v) vars)

let pp_print_contract_item fmt = function
  | GhostConst c -> pp_print_contract_ghost_const fmt c
  | GhostVar v -> pp_print_contract_ghost_var fmt v
  | Assume a -> pp_print_contract_assume fmt a
  | Guarantee g -> pp_print_contract_guarantee fmt g
  | Mode m -> pp_print_contract_mode fmt m
  | ContractCall call -> pp_print_contract_call fmt call
  | AssumptionVars vars -> pp_print_contract_assump_vars fmt vars


let pp_print_contract fmt contract =
  Format.fprintf fmt "@[<v>%a@]"
    (pp_print_list pp_print_contract_item "@ ") contract

let pp_print_contract_spec ppf = function
| None -> ()
| Some contract ->
  Format.fprintf 
    ppf
    "@[<v 2>(*@contract@ %a@]@ *)@ "
    pp_print_contract contract


(* Pretty-prints a contract node. *)
let pp_print_contract_node_decl ppf (n,p,i,o,e)
 =
     Format.fprintf
       ppf
       "@[<hv>@[<hv 2>contract %a%t@ \
        @[<hv 1>(%a)@]@;<1 -2>\
        returns@ @[<hv 1>(%a)@];@]@.\
        @[<hv 2>let@ \
        %a@;<1 -2>\
        tel;@]@]@?"
       pp_print_ident n
       (function ppf -> pp_print_node_param_list ppf p)
       (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
       (pp_print_list pp_print_clocked_typed_ident ";@ ") o
       pp_print_contract e

let pp_print_node_or_fun_decl is_fun ppf (
  _, (n, ext, p, i, o, l, e, r)
) =
    Format.fprintf ppf
      "@[<hv>@[<hv 2>%s%s %a%t@ \
      @[<hv 1>(%a)@]@;<1 -2>\
      returns@ @[<hv 1>(%a)@];@]@.\
      %a@?\
      %a@?\
      @[<v 2>let@ \
      %a@;<1 -2>\
      tel;@]@]@?"
      (if is_fun then "function" else "node")
      (if ext then " imported" else "")
      pp_print_ident n 
      (function ppf -> pp_print_node_param_list ppf p)
      (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
      (pp_print_list pp_print_clocked_typed_ident ";@ ") o
      pp_print_contract_spec r
      pp_print_node_local_decl l
      (pp_print_list pp_print_node_item "@ ") e

(*type t_node_decl = *)

(* Pretty-print a declaration *)
let pp_print_declaration ppf = function

  | TypeDecl (_, t) -> 

    Format.fprintf ppf "type %a;" LustreAst.pp_print_type_decl t

  | ConstDecl (_, c) -> LustreAst.pp_print_const_decl ppf c

  | NodeDecl (span, decl) ->
    pp_print_node_or_fun_decl false ppf (span, decl)

  | FuncDecl (_, _) 
  | ContractNodeDecl (_, _) 
  | NodeParamInst (_, (_, _, _)) -> 
    Format.fprintf ppf "@[[not supported];@]"

(* eof *)