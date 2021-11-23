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

(** 
    @author Andrew Marmaduke *)

module IMap : sig
  (* everything that [Stdlib.Map] gives us  *)
  include (Map.S with type key = LustreAst.ident)
  val keys: 'a t -> key list
end

type context

val empty_context: context

val get_type: context -> LustreAst.ident -> LustreAst.ident -> LustreAst.lustre_type option

val union: context -> context -> context

val interpret_program: TypeCheckerContext.tc_context -> LustreAst.t -> context
