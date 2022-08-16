(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(** Statistics 

    @author Christoph Sticksel *)

(** An integer statistics item *)
type int_item 

(** A float statistics item *)
type float_item 

(** An integer statistics list *)
type int_list_item 

(** An generic statistics item *)
type stat_item 

(** {1 Accessor functions} *)

(** Set an integer statistics item *)
val set : int -> int_item -> unit 

(** Set a float statistics item *)
val set_float : float -> float_item -> unit 

(** Set an integer statistics list *)
val set_int_list : int list -> int_list_item -> unit 

(** Increment an integers statistics item *)
val incr : ?by:int -> int_item -> unit 

(** Increment the last element of an integers statistics list *)
val incr_last : ?by:int -> int_list_item -> unit 

(** Append at the end of an integers statistics list *)
val append : int -> int_list_item -> unit 

(** Reset an integer statistics item to its initial value *)
val reset : int_item -> unit 

(** Reset a float statistics item to its initial value *)
val reset_float : float_item -> unit 

(** Reset an integer list statistics item to its initial value *)
val reset_int_list : int_list_item -> unit 

(** Get the value of an integer statistics item *)
val get : int_item -> int 

(** Get the value of a float statistics item *)
val get_float  : float_item -> float

(** Get the value of an integer statistics list *)
val get_int_list : int_list_item -> int list

(** Start a timer for the float statistics item

    The timer (re-)starts from zero, a previously started time will
    be reset. *)
val start_timer : float_item -> unit

(** Record the time since the call to {!start_timer} of this
    statistics item, stop the timer *)
val record_time : float_item -> unit

(** Unpauses a timer previously paused by [record_time]. *)
val unpause_time : float_item -> unit

(** Record the time since the call to {!start_timer} of this
    statistics item, do not stop the timer *)
val update_time : float_item -> unit

(** Time a function call and add to the statistics item *)
val time_fun :  float_item -> (unit -> 'a) -> 'a

(*
(** Suspend the timer for the float statistics item

    The value of the timer is not committed to the statistics item,
    continue with {!continue_timer} *)
val suspend_timer : float_timer -> unit

(** Continue the previously suspended timer for the float statistics item *)
val continue_timer : float_timer -> unit
*)


(** {1 Pretty-printing} *)

(** {1 Statistics items} *)

(** Print statistics  *)
val pp_print_stats : Format.formatter -> stat_item list -> unit 

(** Print statistics in XML *)
val pp_print_stats_xml : Format.formatter -> stat_item list -> unit 

(** Print statistics in JSON *)
val pp_print_stats_json : Format.formatter -> stat_item list -> unit

(** {2 BMC} *)

(** Highest k reached *)
val bmc_k : int_item 

(** Total time in BMC *)
val bmc_total_time : float_item

(** Stop and record all timers *)
val bmc_stop_timers : unit -> unit 

(** Title for BMC statistics *)
val bmc_stats_title : string

(** BMC statistics *)
val bmc_stats : stat_item list

(** Print statistics for BMC *)
val pp_print_bmc_stats : Format.formatter -> unit 

(** {2 Inductive step} *)

(** Highest k reached *)
val ind_k : int_item 

(** Number clauses to compress inductive counterexamples *)
val ind_compress_equal_mod_input : int_item 

(** Number clauses to compress inductive counterexamples *)
val ind_compress_same_successors : int_item 

(** Number clauses to compress inductive counterexamples *)
val ind_compress_same_predecessors : int_item 

(** Number of restarts *)
val ind_restarts : int_item 

(** Total time in BMC *)
val ind_lazy_invariants_count : int_item

(** Total time in BMC *)
val ind_lazy_invariants_time : float_item

(** Total time in BMC *)
val ind_total_time : float_item

(** Stop and record all timers *)
val ind_stop_timers : unit -> unit 

(** Title for inductive step statistics *)
val ind_stats_title : string

(** Inductive step statistics *)
val ind_stats : stat_item list

(** Print statistics for inductive step *)
val pp_print_ind_stats : Format.formatter -> unit 

(** {2 IC3} *)

(** Highest k reached *)
val ic3_k : int_item 

(** Number of restarts *)
val ic3_restarts : int_item 

(** Frame sizes in *)
val ic3_frame_sizes : int_list_item

(** Number of forward propagations *)
val ic3_fwd_propagated : int_item

(** Number of forward propagations without generalization *)
val ic3_fwd_gen_propagated : int_item

(** Number of forward subsumed clauses *)
val ic3_fwd_subsumed : int_item

(** Number of backward subsumed clauses *)
val ic3_back_subsumed : int_item

(** Fixpoint in forward propagation *)
val ic3_fwd_fixpoint : int_item

(** Blocking clauses proved inductive *)
val ic3_inductive_blocking_clauses : int_item

(** Total time in IC3 *)
val ic3_total_time : float_item

(** Time spent forward propagating *)
val ic3_fwd_prop_time : float_item

(** Time spent strengthening *)
val ic3_strengthen_time : float_item

(** Time spent searching counterexamples *)
val ic3_find_cex_time : float_item

(** Time spent inductively generalizing counterexample *)
val ic3_ind_gen_time : float_item

(** Time spent generalizing *)
val ic3_generalize_time : float_item

(** Time checking inductiveness of blocking clauses *)
val ic3_inductive_check_time : float_item

(** Number of activation literals *)
val ic3_activation_literals : int_item
  
(** Number of permanently false activation literals *)
val ic3_stale_activation_literals : int_item
  
(** Stop and record all timers *)
val ic3_stop_timers : unit -> unit 

(** Title for IC3 statistics *)
val ic3_stats_title : string

(** IC3 statistics *)
val ic3_stats : stat_item list

(** Print statistics for IC3 *)
val pp_print_ic3_stats : Format.formatter -> unit

(** Indices of discoveredi interpolants relative to end of frame *)
val ic3ia_refinements : int_list_item

(** Indices of discoveredi interpolants relative to end of frame *)
val ic3ia_refinements_end : int_list_item
                              
(** Number of abstraction refinements *)
val ic3ia_num_simulations : int_item

(** Total time for interpolation *)
val ic3ia_interpolation_time : float_item

(** Title for IC3IA statistics *)
val ic3ia_stats_title : string
                    
(** IC3IA statistics *)
val ic3ia_stats : stat_item list

(** Print statistics for IC3IA *)
val pp_print_ic3ia_stats : Format.formatter -> unit

(** {2 INVGENOS} *)

(** Hightest k reached. *)
val invgengraph_os_k : int_item

(** Total number of candidate terms. *)
val invgengraph_os_candidate_term_count : int_item

(** Total number of invariants discovered by invariant generation for
    all systems. *)
val invgengraph_os_invariant_count : int_item

(** Total number of invariants discovered by invariant generation
    which were implications. *)
val invgengraph_os_implication_count : int_item

(** Time spent rewriting graphs. *)
val invgengraph_os_graph_rewriting_time : float_item

(** Time spent rewriting graphs. *)
val invgengraph_os_total_time : float_item

(** Title for INVGENOS statistics *)
val invgengraph_os_stats_title : string

(** All INVGENOS statistics *)
val invgengraph_os_stats : stat_item list

(** Stop and record all timers *)
val invgengraph_os_stop_timers : unit -> unit

(** Pretty-print INVGENOS statistics items *)
val pp_print_invgengraph_os_stats : Format.formatter -> unit


(** {2 INVGENTS} *)

(** Hightest k reached. *)
val invgengraph_ts_k : int_item

(** Total number of candidate terms. *)
val invgengraph_ts_candidate_term_count : int_item

(** Total number of invariants discovered by invariant generation for
    all systems. *)
val invgengraph_ts_invariant_count : int_item

(** Total number of invariants discovered by invariant generation
    which were implications. *)
val invgengraph_ts_implication_count : int_item

(** Time spent rewriting graphs. *)
val invgengraph_ts_graph_rewriting_time : float_item

(** Time spent rewriting graphs. *)
val invgengraph_ts_total_time : float_item

(** Title for INVGENTS statistics *)
val invgengraph_ts_stats_title : string

(** All INVGENTS statistics *)
val invgengraph_ts_stats : stat_item list

(** Stop and record all timers *)
val invgengraph_ts_stop_timers : unit -> unit

(** Pretty-print INVGENTS statistics items *)
val pp_print_invgengraph_ts_stats : Format.formatter -> unit


(** {2 C2I} *)

(** Number of strengthening invariants found. *)
val c2i_str_invs : int_item

(** Number of zero-cost candidates found. *)
val c2i_zero_cost : int_item

(** Number of random moves made. *)
val c2i_moves : int_item

(** Time spent in moving and evaluating. *)
val c2i_move_time : float_item

(** Time spent querying solvers. *)
val c2i_query_time : float_item

(** Time spent comparing models. *)
val c2i_model_comp_time : float_item

(** Total time. *)
val c2i_total_time : float_item

(** Title for C2I statistics. *)
val c2i_stats_title : string

(** All C2I statistics. *)
val c2i_stats : stat_item list

(** Stop and record all timers. *)
val c2i_stop_timers : unit -> unit

(** Pretty-print C2I statistics items *)
val pp_print_c2i_stats : Format.formatter -> unit

(** {2 Testgen} *)

(* Number of testcases generated. *)
val testgen_testcases: int_item

(* Number of deadlocks found. *)
val testgen_deadlocks: int_item

(* Number of restarts performed. *)
val testgen_restarts: int_item

(** Time spent going forward. *)
val testgen_forward_time: float_item

(** Time spent going backward. *)
val testgen_backward_time: float_item

(** Time spent enumerating. *)
val testgen_enumerate_time: float_item

(* Total runtime for testgen. *)
val testgen_total_time: float_item

(* Title for testgen statistics *)
val testgen_stats_title: string

(* All testgen statistics *)
val testgen_stats: stat_item list

(* Stop and record all times *)
val testgen_stop_timers: unit -> unit

(* Pretty-print testgen statistics items *)
val pp_print_testgen_stats: Format.formatter -> unit

(** {2 SMT} *)

(** Time in check-sat calls *)
val smt_check_sat_time : float_item 

(** Time in get-value calls *)
val smt_get_value_time : float_item 

(** Time in get-unsat-core calls *)
val smt_get_unsat_core_time : float_item 

(** Stop and record all timers *)
val smt_stop_timers : unit -> unit 

(** Title for SMT statistics *)
val smt_stats_title : string

(** SMT statistics *)
val smt_stats : stat_item list

(** Print statistics for SMT *)
val pp_print_smt_stats : Format.formatter -> unit 

(** {2 Certificates} *)

val certif_gen_time : float_item 
val certif_min_time : float_item 
val certif_frontend_time : float_item 
val certif_cvc5_time : float_item 
val certif_k : int_item 
val certif_size : int_item 
val certif_old_k : int_item 
val certif_old_size : int_item 

val certif_stop_timers : unit -> unit 

(** Title for certificate statistics *)
val certif_stats_title : string

(** Certificate statistics *)
val certif_stats : stat_item list

(** Print statistics for certificate *)
val pp_print_certif_stats : Format.formatter -> unit 


(** {2 Misc.} *)

(** Total time *)
val total_time : float_item

val analysis_time : float_item

val clause_of_term_time : float_item

val smtexpr_of_term_time : float_item

val term_of_smtexpr_time : float_item

(** Stop and record all timers *)
val misc_stop_timers : unit -> unit 

(** Title of the general statistics section *)
val misc_stats_title : string

(** General statistics *)
val misc_stats : stat_item list 

(** Print general statistics *)
val pp_print_misc_stats : Format.formatter -> unit 

val remaining_timeout : unit -> float

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
