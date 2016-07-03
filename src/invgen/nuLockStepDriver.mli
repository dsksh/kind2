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


(** The base checker is used to check whether some candidate invariants hold
[k] steps away from the initial state. *)
type base

(** Kills a base checker. *)
val kill_base : base -> unit

(** Creates a base checker for some system at some depth. *)
val mk_base_checker : TransSys.t -> Numeral.t -> base

(** Adds some invariants to a base checker. *)
val base_add_invariants : base -> (Term.t * Certificate.t) list -> unit

(** Checks whether some terms are falsifiable [k] states away from the initial
state, where [k] is the internal depth of the base checker.

Returns an option of a model falsifying some of the terms. *)
val query_base : base -> Term.t list -> Model.t option




(** The step checker is used to check whether some candidate invariants hold in
the [k]-inductive step instance. *)
type step

(** Kills a step checker. *)
val kill_step : step -> unit

(** Transforms a base checker into a step checker.

The step checker thus obtained correspond to the [k]-induction step instance
the base checker corresponds to. That is, the transition relation is unrolled
one step further and the initial state constraint is removed. *)
val to_step : base -> step

(** Adds invariants to a step checker. *)
val step_add_invariants : step -> (Term.t * Certificate.t) list -> unit

(** Queries step.

Takes some [candidates], a list of elements of type [(Term.t, 'a)]. The second
element is understood as some information about the candidate.

The "information" represented by ['a] is used when checking equality candidate
invariants coming from equivalence classes from the graph. The info is then a
pair representative / eq class member meaning that if the candidate is indeed
invariant, we can drop the class member from the equivalence class.

Returns the elements of [candidates] for which the first element of the pair
(the term) is an invariant. *)
val query_step : bool -> step -> (Term.t * 'a) list -> (Term.t * 'a) list




(** Used to check whether some invariants are implied by the transition
relation alone. That is, [T(0,1) and (not inv(1))] is unsat. *)
type pruning

(** Kills a pruning checker. *)
val kill_pruning : pruning -> unit

(** Creates a pruning checker for a system. *)
val mk_pruning_checker : TransSys.t -> pruning

(** Adds invariants to a pruning checker. *)
val pruning_add_invariants : pruning -> (Term.t * Certificate.t) list -> unit

(** Checks if some terms are trivially implied by the transition relation.

Returns a pair of the trivial and the non-trivial invariants. *)
val query_pruning : pruning -> Term.t list -> ( Term.t list * Term.t list )

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)