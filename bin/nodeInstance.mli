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

type prop = { id : int; vars : svar_instance list; expr : LustreExpr.t; }

val instantiate_node_name : LustreIdent.t -> 'a -> SV.t * 'a list
val id_of_node_instance : 'a * 'b list -> 'b
val instantiate_svar : SV.t * 'a -> (SV.t * 'a) SVT.t -> SVT.key -> SV.t * 'a
val instantiate_svar_trie :
  SV.t * 'a -> (SV.t * 'a) SVT.t -> SVT.key D.t -> (SV.t * 'a) list
val register_arg : (SV.t * 'a) SVT.t -> SV.t * 'a -> SVT.key -> SV.t -> unit
val mk_sv_from_svi : ?is_const:bool -> SV.t * int list -> SV.t
val mk_subst_sv : (SV.t * int list) SVT.t -> SVT.key -> SV.t
val mk_subst_var :
  (SV.t * int list) option -> (SV.t * int list) SVT.t -> Var.t -> Var.t
val mk_observable : LustreNode.t -> LustreNode.t
val instantiate_node :
  LustreNode.t list ->
  int -> svar_instance SVT.t -> LustreNode.t -> 
  node_instance * node_instance list * int
val instantiate_child :
  LustreNode.t list ->
  SV.t * int list ->
  svar_instance SVT.t ->
  LustreNode.node_call -> 
  node_instance list * node_instance list * int ->
  node_instance list * node_instance list * int
val instantiate_main_nodes : LustreNode.t list -> node_instance list * int
val collect_props :
  SV.t * int list ->
  svar_instance SVT.t ->
  LustreExpr.t SVT.t ->
  LustreContract.svar -> 
  prop list * int list -> 
  prop list * int list
val collect_props_from_contract :
  node_instance -> 
  prop list * (int * int list * int list * int list * int list) list * (int * int list * int list) list ->
  prop list * (int * int list * int list * int list * int list) list * (int * int list * int list) list
val translate_subsystems :
  'a InputSystem.t ->
  node_instance list * prop list * (int * int list * int list * int list * int list) list * (int * int list * int list) list

val pp_print_svar_instance :
  (SV.t * int list) option -> Format.formatter -> SV.t * int list -> unit
val pp_print_svi_typed :
  (SV.t * int list) option -> Format.formatter -> SV.t * int list -> unit
val pp_print_map :
  (SV.t * int list) option ->
  Format.formatter -> (SV.t * int list) SVT.t -> unit
val pp_print_node : Format.formatter -> node_instance -> unit
val pp_print_nodes : Format.formatter -> node_instance list -> unit
val pp_print_prop : Format.formatter -> prop -> unit
val pp_print_props : Format.formatter -> prop list -> unit
