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

(* Abbreviations *)
module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module C = LustreContext

module SVS = StateVar.StateVarSet 


(* ********************************************************************** *)
(* Dependency order of definitions and cycle detection                    *)
(* ********************************************************************** *)

(* For each state variable return the list of state variables in the
   current instant that are used in its definition, and transitively
   in their definitions, and fail if the definitions contain a
   cycle. 

   We don't need to consider assertions and node calls here, since we
   only need the ordering only to sort equations and detect cycles.

   We could find potential cycles when a node does not have an
   implementation, but this is more trouble than it's worth. We need
   to distinguish between strong and weak dependencies. If variable is
   undefined, it weakly depends on all inputs. Then we can find weak
   dependencies through nodes where an input is
   underspecified. However, we then need to eliminate that cycle by
   backtracking over the children we explored and that's where the
   troubles start. *)
let rec node_state_var_dependencies' 
    init
    output_input_deps
    ({ N.inputs; N.equations; N.calls } as node)
    accum = 

  (* Return true if the state variable occurs on a path of
     dependencies in its parents *)
  let rec has_cycle state_var = function 

    (* First dependency *)
    | sv :: tl -> 

      (* State variable occurs as its parent? *)
      StateVar.equal_state_vars sv state_var || 
      has_cycle state_var tl

    (* No more dependencies *)
    | [] -> false

  in

  function 

    (* Return all calculated dependencies *)
    | [] -> accum

    (* Calculate dependency of variable [state_var], which all
       variables in [parents] depend on *)
    | (state_var, parents) :: tl -> 

      if 

        (* Is there a strong dependency cycle with the state
           variable? *)
        has_cycle state_var parents

      then

        (* Output variables in circular dependency, drop variables
           that are not visible in the origial source *)
        C.fail_no_position 
          (Format.asprintf
             "Circular dependency: %a@."
             (pp_print_list
                (E.pp_print_lustre_var false) 
                " -> ")
             (List.filter N.state_var_is_visible  (state_var :: parents)))

      else

        (* All state variables at the current instant in the equation
           or node call defining the state variable *)
        let children = 

          try 

            (* State variable is defined in an equation? *)
            List.find
              (fun (sv, _, _) -> 
                 StateVar.equal_state_vars sv state_var)
              equations

            |> 

            (* State variable depends on state variables in equation *)
            (function (sv, _, expr) ->
              (if init then 
                 E.base_state_vars_of_init_expr 
               else
                 E.cur_state_vars_of_step_expr)
                expr
              |> SVS.elements)

          (* State variable is not constrained by an equation *)
          with Not_found -> 

            try 

              (* State variable is defined by a node call? *)
              List.find
                (fun { N.call_outputs } -> 
                   D.exists 
                     (fun _ sv -> StateVar.equal_state_vars state_var sv)
                     call_outputs)
                calls

              |>

              (function
                  { N.call_node_name; 
                    N.call_inputs; 
                    N.call_oracles; 
                    N.call_outputs; 
                    N.call_observers;
                    N.call_defaults;
                    N.call_clock } -> 

                  (* Index of state variable in outputs *)
                  let output_index = 

                    try

                      (* Find state variable in outputs and return its
                         index *)
                      D.bindings call_outputs 
                      |> List.find
                        (fun (_, sv) -> 
                           StateVar.equal_state_vars state_var sv)
                      |> fst

                    (* State variable is an output, has been found before *)
                    with Not_found -> assert false 

                  in

                  (* Get computed dependencies of outputs on inputs
                     for called node *)
                  let output_input_dep =

                    try 

                      List.assoc call_node_name output_input_deps

                      |> if init then fst else snd

                    (* Node of name not found *)
                    with Not_found -> D.empty

                  in

                  (* Get indexes of inputs the output depends on *)
                  (try 

                     D.find output_index output_input_dep

                   (* All outputs must have dependencies computed *)
                   with Not_found -> assert false)

                  |> 

                  (List.fold_left
                     (fun accum i -> 

                        (* Get actual input by index, and add as
                           dependency *)
                        try SVS.add (D.find i call_inputs) accum 

                        (* Invalid map *)
                        with Not_found -> assert false)
                     SVS.empty)

                  |> 

                  (* Defaults of a condact are children *)
                  (function children ->

                    (* Only if computing dependencies in the initial
                       state *)
                    if init then 

                      (* Add state variables at the initial state from
                         the default expressions *)
                      D.fold
                        (fun _ default accum -> 
                           E.base_state_vars_of_init_expr default
                           |> SVS.union accum)
                        call_defaults
                        children

                    else

                      (* Default expressions are only evaluated at the
                         initial state *)
                      children)

                  |> 

                  (* Clock of condact is a child *)
                  (function children -> 
                    match call_clock with 
                      | None -> children
                      | Some clk -> SVS.add clk children)

                  |>

                  (* Return list of elements of a set *)
                  SVS.elements)

            (* State variable is neither defined by an equation nor by a
               node call *)
            with Not_found -> []

        in

        (* Some variables have had their dependencies calculated
           already *)
        let children_visited, children_not_visited =
          List.partition
            (fun sv -> 
               List.exists
                 (fun (sv', _) -> StateVar.equal_state_vars sv sv')
                 accum)
            children
        in

        (* All children visited? *)
        if children_not_visited = [] then 

          (* Dependencies of this variable is set of dependencies of its
             variables *)
          let children = 

            List.fold_left

              (fun a sv -> 

                 try 

                   (* Add child as strong dependency to accumulator *)
                   SVS.union
                     a
                     (SVS.singleton sv)

                   |>

                   (* Add grandchildren as strong or weak dependencies *)
                   SVS.union
                     (List.find 
                        (fun (sv', _) -> StateVar.equal_state_vars sv sv')
                        accum |> snd)

                 with Not_found -> assert false)

              SVS.empty
              children_visited

          in

          (* Add variable and its dependencies to accumulator *)
          node_state_var_dependencies' 
            init
            output_input_deps
            node 
            ((state_var, children) :: accum)
            tl

        else

          (* First get dependencies of all dependent variables *)
          node_state_var_dependencies' 
            init
            output_input_deps
            node
            accum 
            ((List.map 
                (fun sv -> (sv, state_var :: parents)) 
                children_not_visited) @ 
             ((state_var, parents) :: tl))


(* Given an association list of state variables to the set of the
   state variables they depend on, return the state variables in
   toplogical order 

   There must be no cyclic dependencies, otherwise this function will
   loop forever. *)
let rec order_state_vars accum = function

  (* All variables in the accumulator *)
  | [] -> accum

  (* Skip if state variable is already in the accumulator *)
  | (h, _) :: tl when List.mem h accum -> order_state_vars accum tl

  (* State variable and the variables it depends on *)
  | (h, d) :: tl -> 
    
    if 

      (* All dependencies of state variables in the accumulator? *)
      SVS.for_all (fun sv -> List.mem sv accum) d

    then

      (* Add state variable to accumulator and continue *)
      order_state_vars (h :: accum) tl
      
    else

      (* Push all dependent variables to the top of the stack *)
      let tl' = 
        SVS.fold
          (fun sv a -> 
             try 
               (* Find dependencies of state variable *)
               (List.find 
                  (fun (sv', _) -> StateVar.equal_state_vars sv sv')
                  tl) :: a
             (* All dependent state variables must be in stack *)
             with Not_found -> assert false)
          d
          ((h, d) :: tl)
      in

      (* Must add dependent state variables to accumulator first *)
      order_state_vars accum tl'
      
      
(* Compute dependencies of outputs on inputs 

   Return a trie maps each index of a state variable in the outputs to
   the list of indexes of input state variables the output depends
   on. *)
let output_input_dep_of_dependencies dependencies inputs outputs = 

  (* Map trie of output state variables to trie of indexes *)
  D.mapi

    (fun j output -> 

       (* State variables this state variables depends on *)
       let output_dep = 

         try

           (* Get state variables the state variable depends on *)
           List.find 
             (fun (sv', _) -> StateVar.equal_state_vars output sv')
             dependencies

           |> snd 

         (* All dependencies must have been computed *)
         with Not_found -> assert false

       in

       (* Get indexes of all state variables that are inputs *)
       SVS.fold
         (fun sv a -> 

            match 

              (* Find state variable in inputs *)
              D.filter
                (fun _ sv' -> StateVar.equal_state_vars sv sv')
                inputs 
              |> D.keys

            with 

              (* State variable is not an input *)
              | [] -> a

              (* Add index of state variable in input to
                 accumulator *)
              | [i] -> i :: a

              (* State variable occurs in input twice *)
              | _ -> assert false)

         output_dep
         [])

    outputs


(* Order equations of node topologically by their dependencies to have
   leaf equations first, and set the map of outputs to the inputs they
   depend on *)
let order_equations 
    init
    output_input_deps
    ({ N.inputs; N.outputs; N.equations; N.calls } as node) = 

  (* Compute dependencies for state variables on the left-hand side of
     definitions, that is, in equations and node calls *)
  let state_vars = 

    (* State variables on the left-hand side of equations *)
    (List.map (fun (sv, _, _) -> (sv, [])) equations
       
    |> D.fold
         (fun _ sv a -> (sv, []) :: a)
         outputs

     (* Add state variables capturing outputs of node calls *)
     |> (fun accum -> 
         List.fold_left
           (fun a { N.call_outputs } -> 
              D.fold 
                (fun _ sv a -> (sv, []) :: a)
                call_outputs
                a)
           accum
           calls))

  in

  (* Compute dependencies of state variable *)
  let dependencies = 
    node_state_var_dependencies'
      init
      output_input_deps
      node
      []
      state_vars
  in

  (* Order state variables by dependencies *)
  let state_vars_ordered = order_state_vars [] dependencies in

  (* Order equations by state variables *)
  let equations' = 
    List.fold_left
      (fun a sv ->

         try 

           (* Find equation of state variable and add to
              accumulator *)
           List.find 
             (fun (sv', _, _) -> StateVar.equal_state_vars sv sv')
             equations
             :: a

         (* State variable may be output of a node call, or
            unconstrained *)
         with Not_found -> a)

      []
      state_vars_ordered 

  in 

  (* Dependency of output variables on input variables *)
  let output_input_dep = 
    output_input_dep_of_dependencies dependencies inputs outputs
  in

  equations', output_input_dep

          
(* ********************************************************************** *)
(* Cone of influence slicing                                              *)
(* ********************************************************************** *)


(* Initially empty node for slicing *)
let slice_all_of_node 
    { N.name; 
      N.instance;
      N.running;
      N.first_tick;
      N.inputs; 
      N.oracles; 
      N.outputs; 
      N.observers; 
      N.props; 
      N.contracts; 
      N.is_main } = 

  (* Copy of the node with the same signature, but without local
     variables, equations, assertions and node calls. Keep signature,
     properties, contracts and main annotation *)
  { N.name; 
    N.instance;
    N.running;
    N.first_tick;
    N.inputs;
    N.oracles; 
    N.outputs; 
    N.observers; 
    N.locals = [];
    N.equations = [];
    N.calls = [];
    N.asserts = [];
    N.props;
    N.contracts;
    N.is_main }


(* Add roots of cone of influence from node call to roots *)
let add_roots_of_node_call 
    roots
    { N.call_clock; 
      N.call_inputs; 
      N.call_oracles; 
      N.call_defaults } =

  (* Add dependencies from defaults as roots *)
  let roots' =
    D.fold
      (fun _ e a -> 
         (E.state_vars_of_expr e |> SVS.elements) @ a) 
      call_defaults
      roots
  in

  (* Add inputs, oracles and clock as roots *)
  let roots' = 

    (* Need dependecies of inputs to node call *)
    D.values call_inputs @ 

    (* Need dependencies of oracles *)
    call_oracles @ 

    (* Need dependencies of clock if call has one *)
    (match call_clock with
      | None -> roots'
      | Some c -> c :: roots')

  in

  (* Return with new roots added *)
  roots'


(* Add roots of cone of influence from equation to roots *)
let add_roots_of_equation roots (_, _, expr) = 
  (E.state_vars_of_expr expr |> SVS.elements) @ roots


(* Return state variables from properties *)
let roots_of_props = List.map fst


(* Return state variables from contracts *)
let roots_of_contracts (global_contract, mode_contracts) = 

  (* State variables in a contract are requirements and ensures *)
  let roots_of_contract 
    { N.contract_reqs; N.contract_enss } = contract_reqs @ contract_enss
  in

  (* Combine state variables from global contract and mode
     contracts *)
  List.fold_left 
    (fun a (_, c) -> roots_of_contract c @ a)
    (match global_contract with
      | None -> []
      | Some c -> roots_of_contract c)
    mode_contracts


(* Reduce nodes to cone of influence

   The last argument is a stack of quadruples [(roots, leaves, sliced,
   unsliced)]. For each state variable in [roots], all [equations],
   [asserts], [calls] and [locals] that mention the state variable are
   to be moved from the node [unsliced] to the node [sliced]. If the
   state variable is in [leaves], either the state variables mentioned
   in equations, asserts or node calls are already in [roots], or the
   definitions of the state variable should not be expanded. 

   If a state variable in [roots] is defined by a node call, find the
   called node in [nodes], obtain an initial quadruple for the stack
   with [init_slicing_of_node] and push it to the top of the stack so
   that the called node is sliced first. 

   Call this function with *)
let rec slice_nodes init_slicing_of_node nodes accum = function 

  (* All nodes are sliced and in the accumulator *)
  | [] -> accum

  (* Node is sliced to all equations *)
  | ([], leaves, ({ N.name } as node_sliced), node_unsliced) :: tl -> 

    (* Sort equations of sliced node by dependencies, and continue

       We must pass [accum] instead of [nodes] to order_equations,
       because we need the output input dependencies of called nodes
       that are only set when adding a node to [accum]. *)
    slice_nodes
      init_slicing_of_node
      nodes
      (node_sliced :: accum)
      tl

  (* State variable is a leaf, that is no dependencies have to be
     added, because it has been visited, or should not be expanded *)
  | (state_var :: roots_tl, leaves, node_sliced, node_unsliced) :: tl 
    when List.exists (StateVar.equal_state_vars state_var) leaves -> 

    slice_nodes
      init_slicing_of_node
      nodes
      accum
      ((roots_tl, leaves, node_sliced, node_unsliced) :: tl)

  (* State variable is not a leaf, need to add all dependencies *)
  | (state_var :: roots', 
     leaves, 
     ({ N.equations = equations_in_coi;
        N.asserts = asserts_in_coi;
        N.calls = calls_in_coi;
        N.locals = locals_in_coi } as node_sliced),
     ({ N.equations = equations_not_in_coi; 
        N.asserts = asserts_not_in_coi;
        N.calls = calls_not_in_coi;
        N.locals = locals_not_in_coi } as node_unsliced)) :: tl as l -> 

    try 

      (* State variable is an output or an observer of a called node
         that is not already sliced? *)
      let { N.call_node_name } =
        List.find
          (function { N.call_node_name; N.call_outputs; N.call_observers } ->

            (* Called node is not already sliced? *)
            (not (N.exists_node_of_name call_node_name accum)

             &&

             (* State variable is an output of the called node? *)
             (D.exists
                (fun _ sv -> StateVar.equal_state_vars state_var sv)
                call_outputs

              || 

              (* State variable is an observer of the called node? *)
              List.exists 
                (StateVar.equal_state_vars state_var)
                call_observers)))
          calls_not_in_coi
      in

      (* Get called node by name *)
      let node = N.node_of_name call_node_name nodes in

      (* Slice called node first, then return to this node

         TODO: Detect cycles in node calls here, but that should not
         be possible with the current format. *)
      slice_nodes
        init_slicing_of_node
        nodes
        accum
        (init_slicing_of_node node :: l)

    (* State variable is not defined by a node call *)
    with Not_found -> 

      (* Equations with defintion of variable added, and new roots
         from dependencies of equation *)
      let equations_in_coi', equations_not_in_coi', roots' = 

        List.fold_left 

          (fun
            (equations_in_coi, equations_not_in_coi, roots')
            ((sv, _, expr) as eq) -> 

            (* Equation defines variable? *)
            if StateVar.equal_state_vars state_var sv then

              (* Add equation to sliced node *)
              (eq :: equations_in_coi, 

               (* Remove equation from unsliced node *)
               equations_not_in_coi,

               (* Add variables in equation as roots *)
               add_roots_of_equation roots' eq)
              
            else

              (* Do not add equation to sliced node, keep in unsliced
                 node, and no new roots *)
              (equations_in_coi, eq :: equations_not_in_coi, roots')
               
          )

          (* Modify equations in sliced and unsliced node, and roots *)
          (equations_in_coi, [], roots')

          (* Iterate over all equations in unsliced node *)
          equations_not_in_coi

      in

      (* Node calls with call returning state variable added, and new
         roots from dependencies of node call *)
      let calls_in_coi', calls_not_in_coi', roots' = 

        List.fold_left 
          
          (fun
            (calls_in_coi, calls_not_in_coi, roots')
            ({ N.call_node_name; 
               N.call_outputs; 
               N.call_observers } as node_call) ->

            if
              
                (* State variable is an output of the called node? *)
                (LustreIndex.exists
                   (fun _ sv -> StateVar.equal_state_vars state_var sv)
                   call_outputs
                 || 

                 (* State variable is an observer of the called node? *)
                 List.exists 
                   (StateVar.equal_state_vars state_var)
                   call_observers)

            then
              
              (* Add equation to sliced node *)
              (node_call :: calls_in_coi, 

               (* Remove equation from unsliced node *)
               calls_not_in_coi,

               (* Add variables in equation as roots *)
               add_roots_of_node_call roots' node_call)
              

            else

              (* Do not add node call to sliced node, keep in unsliced
                 node, and no new roots *)
              (calls_in_coi, node_call :: calls_not_in_coi, roots')

          )

          (* Modify node calls in sliced and unsliced node, and roots *)
          (calls_in_coi, [], roots')

          (* Iterate over all node calls in unsliced node *)
          calls_not_in_coi

      in
  
      (* Add all assertions containing the state variable to sliced
         node, and all state variables in those assertion as roots *)
      let asserts_in_coi', asserts_not_in_coi', roots' = 

        List.fold_left

          (fun (asserts_in_coi, asserts_not_in_coi, roots) expr -> 

             (* State variables in assertion *)
             let s = E.state_vars_of_expr expr in

             (* Assertion contains state variable? *)
             if SVS.mem state_var s then

               (* Add assertion to sliced node *)
               (expr :: asserts_in_coi, 

                (* Remove assertion from unsliced node *)
                asserts_not_in_coi,

                (* Add variables in assertion as roots *)
                SVS.elements s @ roots)

             else

               (* Do not add assertions to sliced node, keep in
                  unsliced node, and no new roots *)
               (asserts_in_coi, expr :: asserts_not_in_coi, roots))

          (* Modify assertions in sliced and unsliced node, and roots *)
          (asserts_in_coi, [], roots')

          (* Iterate over all assertions in unsliced node *)
          asserts_not_in_coi

      in

      (* Move definitions containing the state variable from the
         unsliced to sliced node

         We move definitions of all local variables related by an
         index together. *)
      let locals_in_coi', locals_not_in_coi' = 

        List.fold_left

          (fun (locals_in_coi, locals_not_in_coi) l -> 
             
             if 
               
               (* Local definition contains the state variable? *)
               (D.exists
                  (fun _ sv -> StateVar.equal_state_vars sv state_var))
               l

             then
        
               (* Add all state variables related by an index to this state
                  variable as local variables, but do not add them as roots *)
               (l :: locals_in_coi, locals_not_in_coi)
       
             else

               (* Do not add local variable to sliced node, keep in
                  unsliced node *)
               (locals_in_coi, l :: locals_not_in_coi))

          (* Modify local variables in sliced and unsliced node *)
          (locals_in_coi, [])

          (* Iterate over all local variables in unsliced node *)
          locals_not_in_coi

      in

      (* Modify slicecd node *)
      let node_sliced' =
        { node_sliced with
            N.locals = locals_in_coi';
            N.equations = equations_in_coi';
            N.asserts = asserts_in_coi';
            N.calls = calls_in_coi' } 
      in

      (* Modify slicecd node *)
      let node_unsliced' =
        { node_unsliced with
            N.equations = equations_not_in_coi';
            N.asserts = asserts_not_in_coi';
            N.calls = calls_not_in_coi';
            N.locals = locals_not_in_coi'}
      in

      (* Continue with modified sliced node and roots *)
      slice_nodes
        init_slicing_of_node
        nodes
        accum
        ((roots', (state_var :: leaves), node_sliced', node_unsliced') :: tl)



(* TODO: Slicing to contract version need to look at one node at a
   time only, calls of the node are not relevant. *)

(*

let slice_to_contract =   

  let init_slicing_of_node
      ({ N.inputs; 
         N.oracles; 
         N.outputs; 
         N.observers; 
         N.contracts; 
         N.props } as node) = 

    (* Slice everything from node *)
    let node_sliced = slice_all_of_node node in
    
    (* Get roots and leaves of called node *)
    let node_roots, node_leaves = roots_and_leaves_of_node node_unsliced in
    
    ()

  in

  
  (node_roots, node_leaves, node_sliced, node_unsliced) 

  slice_nodes
    init_slicing_of_node
    nodes
    []
    
*)

(* Slice a node as a top node, starting from its properties and contracts *)
let root_and_leaves_of_props_node 
    ({ N.contracts; 
       N.props } as node) =

  (* Slice everything from node *)
  let node_sliced = slice_all_of_node node in
    
  (* Slice starting with contracts and properties *)
  let node_roots = roots_of_props props @ roots_of_contracts contracts in

  (* Consider all streams *)
  let node_leaves = [] in

  (node_roots, node_leaves, node_sliced, node)
  

(* Slice a node to its implementation, starting from the outputs,
   contracts and properties *)
let root_and_leaves_of_impl  
    ({ N.outputs; 
       N.observers; 
       N.contracts; 
       N.props } as node) =

  (* Slice everything from node *)
  let node_sliced = slice_all_of_node node in

  (* Slice starting with outputs, contracts and properties *)
  let node_roots = 
    D.values outputs @ 
    observers @ 
    roots_of_props props @ 
    roots_of_contracts contracts 
  in

  (* Consider all streams *)
  let node_leaves = [] in

  (node_roots, node_leaves, node_sliced, node)


(* Slice a node to its contracts, starting from contracts, stopping at
   outputs *)
let root_and_leaves_of_contracts
    ({ N.outputs; 
       N.observers; 
       N.contracts; 
       N.props } as node) =

  (* Slice everything from node *)
  let node_sliced = slice_all_of_node node in
    
  (* Slice starting with contracts *)
  let node_roots = 
    roots_of_contracts contracts 
  in

  (* Do not consider anything below outputs *)
  let node_leaves = D.values outputs in

  (node_roots, node_leaves, node_sliced, node)


(* Slice a node to its contracts, starting from contracts, stopping at
   outputs *)
let custom_roots roots node = 

  (* Slice everything from node *)
  let node_sliced = slice_all_of_node node in
    
  (* Slice starting with given roots *)
  let node_roots = roots in

  (* Consider all streams *)
  let node_leaves = [] in

  (node_roots, node_leaves, node_sliced, node)



let slice_to_impl nodes = 

  slice_nodes
    root_and_leaves_of_impl
    nodes
    []
    [(root_and_leaves_of_impl (List.hd nodes))]


let slice_to_contract nodes = 

  slice_nodes
    root_and_leaves_of_contracts
    nodes
    []
    [(root_and_leaves_of_contracts (List.hd nodes))]



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
