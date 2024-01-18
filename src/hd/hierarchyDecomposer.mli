(* Copyright (c) 2024 Daisuke Ishii
*)

(** Entry point *)
(*val main : string -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit*)
val main : 'a InputSystem.t -> unit

(** Cleanup before exit *)
val on_exit : TransSys.t option -> unit