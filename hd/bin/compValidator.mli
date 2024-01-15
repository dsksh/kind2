open NodeInstance

type smod = int
type t =
    M of smod
  | Compat of smod * smod
  | Impl of smod list * smod list
  | Goal of t

val smod : Swipl.ctx -> int -> Swipl.t
val compat : Swipl.ctx -> int -> int -> Swipl.t
val impl : Swipl.ctx -> int list -> int list -> Swipl.t
val goal : Swipl.t -> Swipl.t
val encode : Swipl.ctx -> t list -> Swipl.t
val reducesTo : Swipl.t -> Swipl.t -> Swipl.t
val pp_print_constr : Format.formatter -> t -> unit
val decode : Swipl.ctx -> Swipl.t -> t list

val is_compat_node_pair: node_instance -> node_instance -> t list -> t list
val is_compat_node_prop_pair: node_instance -> prop -> t list -> t list
val is_compat_prop_pair: prop -> prop -> t list -> t list
val enum_compat_pairs : ('a -> 'b -> 'c -> 'c) -> 'a -> 'b list -> 'c -> 'c
val enum_compat_pairs :
  ('a -> 'b -> 'c list -> 'c list) -> 'a list -> 'b list -> 'c list

val translate :
  NodeInstance.node_instance list ->
  NodeInstance.prop list ->
  (smod * smod list * smod list * smod list * smod list) list ->
  (smod * smod list * smod list) list ->
  t list 
val validate : t list -> bool

val pp_print_script : Format.formatter -> t list -> unit