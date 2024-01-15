open Lib
(*open NodeInstance*)
open CompValidator

let prelude = {|
(set-logic AUFLIA)

(set-option :auto_config false)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.phase_selection 0)
(set-option :smt.random_seed 0)

(declare-sort smod 0)
(declare-fun compat (smod smod) Bool)
(declare-fun pc (smod smod) smod)
(declare-fun impl (smod smod) Bool)

;; AG rule.
(assert (forall ((m1 smod) (m2 smod) (ma smod) (mb smod))
  (!
  (=> (and (compat m1 m2) (compat ma mb) 
           (impl (pc m1 mb) ma) (impl (pc m2 ma) mb) ) 
      (impl (pc m1 m2) (pc ma mb)) )
  :pattern ((impl (pc m1 mb) ma) (impl (pc m2 ma) mb)) 
  :pattern (impl (pc m1 m2) (pc ma mb)) 
  )
))

;;; Reflexitivity.
;(assert (forall ((m1 smod)) (impl m1 m1)))
;(assert (forall ((m1 smod)) (compat m1 m1)))

;; Transitivity.
(assert (forall ((m1 smod) (m2 smod) (m3 smod))
  (!
  (=> (and (impl m1 m2) (impl m2 m3) ) 
      (impl m1 m3) )
  :pattern ((impl m1 m2) (impl m2 m3))
  :pattern ((impl m1 m2) (impl m1 m3))
  :pattern ((impl m2 m3) (impl m1 m3))
  )
))

;; Implementation of sub-modules.
(assert (forall ((m1 smod) (m2 smod))
  (!
  (=> (compat m1 m2)
      (impl (pc m1 m2) m1) )
  :pattern (pc m1 m2)
  )
))
(assert (forall ((m1 smod) (m2 smod))
  (!
  (=> (compat m1 m2)
      (impl (pc m1 m2) m2) )
  :pattern (pc m1 m2)
  )
))

;; Commutativity.
(assert (forall ((m1 smod) (m2 smod))
  (!
  (= (pc m1 m2) (pc m2 m1))
  :pattern (pc m1 m2)
  )
))
(assert (forall ((m1 smod) (m2 smod))
  (!
  (= (compat m1 m2) (compat m2 m1))
  :pattern (compat m1 m2)
  )
))

;; Associativity.
(assert (forall ((m1 smod) (m2 smod) (m3 smod))
  (!
  (= (pc (pc m1 m2) m3) (pc m1 (pc m2 m3)))
  :pattern (pc (pc m1 m2) m3) 
  :pattern (pc m1 (pc m2 m3))
  )
))

;; Triangle relationship.
(assert (forall ((m1 smod) (m2 smod) (m3 smod))
  (!
  (=> (and (compat m1 m2) (compat m1 m3) (compat m2 m3))
      (compat (pc m1 m2) m3) )
  :pattern ((compat m1 m2) (compat m1 m3) (compat m2 m3))
  :pattern (compat (pc m1 m2) m3)
  )
))

;;
|}

let rec pp_print_constr ppf constr = 
  let pp_m ppf i = if i >= 0 
    then Format.fprintf ppf "m%d" i
    else Format.fprintf ppf "p%d" (- i) in
  let rec pp_c ppf = function
  | m1::m2::ms -> 
    Format.fprintf ppf "(pc %a %a)" pp_m m1 pp_c (m2::ms)
  | [m] -> 
    pp_m ppf m
  | [] -> failwith "unexpected pp_c call"
  in
  match constr with
  | M i -> 
    Format.fprintf ppf "(declare-const %a smod)" pp_m i
  | Compat (i,j) -> 
    Format.fprintf ppf "(assert (compat %a %a))" pp_m i pp_m j
  | Impl (i,j) -> 
    Format.fprintf ppf "(assert (impl %a %a))" pp_c i pp_c j
  | Goal (Impl (i,j)) -> 
    Format.fprintf ppf "(assert (not (impl %a %a)))" pp_c i pp_c j
  | Goal _ -> 
    failwith "unsupported goal"

let pp_print_script ppf cs =
  Format.fprintf ppf "%s@." prelude;
  Format.fprintf ppf "%a@." (pp_print_list pp_print_constr "@.") cs;
  Format.fprintf ppf "(check-sat)@."

(* eof *)