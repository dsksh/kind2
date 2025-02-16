module I = LustreIdent
module IT = LustreIdent.Hashtbl
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
  is_first : bool;
}

type prop = { id : int; vars : svar_instance list; expr : LustreExpr.t; }

val instantiate_node_name : LustreIdent.t -> int -> svar_instance
val id_of_node_instance : svar_instance -> int
val hd_of_scope : SV.t -> string
val instantiate_svar : SV.t * 'a -> (SV.t * 'a) SVT.t -> SVT.key -> SV.t * 'a
val instantiate_svar_trie :
  SV.t * 'a -> (SV.t * 'a) SVT.t -> SVT.key D.t -> (SV.t * 'a) list
val register_arg : (SV.t * 'a) SVT.t -> SV.t * 'a -> SVT.key -> SV.t -> unit
val mk_sv_from_svi : ?is_const:bool -> SV.t * int -> SV.t
val mk_subst_sv : (SV.t * int) SVT.t -> SVT.key -> SV.t
val mk_subst_var :
  ?inherited:string list option ->
  (SV.t * int) option -> (SV.t * int) SVT.t -> Var.t -> Var.t

val get_prop_rhs : SV.t * int -> svar_instance SVT.t -> LustreExpr.t SVT.t -> 
  LustreContract.svar -> LustreExpr.t * (SV.t*int) list

val translate_subsystems :
  'a InputSystem.t ->
  node_instance list * prop list * (int * int list * int list * int list * int list) list * (int * int list * int list) list

val pp_print_svar_instance :
  (SV.t * int) option -> Format.formatter -> SV.t * int -> unit
val pp_print_svi_typed :
  (SV.t * int) option -> Format.formatter -> SV.t * int -> unit
val pp_print_map :
  (SV.t * int) option ->
  Format.formatter -> (SV.t * int) SVT.t -> unit
val pp_print_node : Format.formatter -> node_instance -> unit
val pp_print_nodes : Format.formatter -> node_instance list -> unit
val pp_print_prop : Format.formatter -> prop -> unit
val pp_print_props : Format.formatter -> prop list -> unit
