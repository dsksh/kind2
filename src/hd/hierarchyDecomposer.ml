(* Copyright (c) 2024 Daisuke Ishii
*)

open Lib

(* Exit and terminate all processes here in case we are interrupted *)
let on_exit _ = 
  ()

type file_oc = Leaves | Proof

let create_ppf input_file t =
  (* Create root dir if needed. *)
  Flags.output_dir () |> mk_dir ;
  (*(* Create smt_trace dir if needed. *)
  let tdir = Flags.Smt.trace_dir () in
  mk_dir tdir ;
  (* Create smt_trace subdir if needed. *)
  let tdir = Filename.concat tdir (Flags.Smt.trace_subdir ()) in
  mk_dir tdir ;*)

  (* Name of the output file *)
  let filename = 
    Filename.concat
      (Flags.output_dir ())
      ( Format.sprintf "%s.%s" (Filename.basename input_file)
        (match t with | Leaves -> "leaves.lus" | Proof -> "proof.pl") )
  in try
    (* Open file for output, may fail *)
    let oc = open_out filename in

    (* Return formatter *)
    Format.formatter_of_out_channel oc

  with Sys_error e -> 
    failwith (Format.asprintf "Failed to open file %s" e)

(* Main entry point *)
let main input_file input_system =

  KEvent.set_module `HierarchyDecomposer;

  KEvent.log L_info "Lustre program parsed";
  KEvent.log L_debug "%a" LustreNodePrinter.pp_print_subsystems input_system;

  let ns, ps, cs, gs = NodeInstance.translate_subsystems input_system in
  KEvent.log L_info "Node instances generated";
  KEvent.log L_debug "%a@." NodeInstance.pp_print_nodes ns;
  KEvent.log L_debug "%a" NodeInstance.pp_print_props ps;

  KEvent.log L_info "Printing leaf node instances";
  let leaves_ppf = create_ppf input_file Leaves in
  Format.fprintf leaves_ppf "%a" NodeInstanceToLustre.pp_print_nodes ns;
  (*KEvent.log L_debug "%a" NodeInstanceToLustre.pp_print_nodes ns;*)

  KEvent.log L_info "Printing a CHR proof script";
  let cs = CompValidator.translate ns ps cs gs in
  let proof_ppf = create_ppf input_file Proof in
  Format.fprintf proof_ppf "%a" CompValidator.pp_print_script cs;
  (*KEvent.log L_debug "%a" CompValidator.pp_print_script cs;*)

  (*if CompValidator.validate cs then
    Format.printf "valid@."
  else
    Format.printf "invalid@.";
  *)
  KEvent.log L_info "Done";

  ()
