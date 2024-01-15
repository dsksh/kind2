open Lib

type file_oc = Leaves | Proof

let create_ppf t =
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
      ( Format.sprintf "%s.%s" (Filename.basename (Flags.input_file ()))
        (match t with | Leaves -> "leaves.lus" | Proof -> "proof.pl") )
  in try
    (* Open file for output, may fail *)
    let oc = open_out filename in

    (* Return formatter *)
    Format.formatter_of_out_channel oc

  with Sys_error e -> 
    failwith (Format.asprintf "Failed to open file %s" e)

let () = 
(* Parse command-line flags. *)
(try
  Flags.parse_argv ()
 with Flags.Error ->
  KEvent.terminate_log () ; exit ExitCodes.error
);

Debug.set_dflags (Flags.debug ()) ;

(* Formatter to write debug output to. *)
(match Flags.debug_log () with
  (* Write to stdout by default. *)
  | None -> ()
  (* Open channel to given file and create formatter on channel. *)
  | Some f ->
    let oc = try open_out f with Sys_error msg ->
      Format.sprintf
        "Could not open debug logfile '%s': '%s'" f msg
      |> failwith
    in
    Debug.set_formatter (Format.formatter_of_out_channel oc)
) ;

let in_file = Flags.input_file () in

KEvent.log L_info "Creating Input system from  %s."
  ( match in_file with
    | "" -> "standard input"
    | _  -> "input file '" ^ in_file ^ "'" );

try
  (*let decls = 
    match LustreInput.ast_of_file in_file with
    | Ok decls -> decls
    | Error e -> LustreReporting.fail_at_position 
        (LustreErrors.error_position e) (LustreErrors.error_message e)
  in
  Format.printf "%a\n" (pp_print_list LustreAst.pp_print_declaration "[end]\n") decls;
  *)

  let input_system = 
    KEvent.log L_debug "Lustre input detected";
    match InputSystem.read_input_lustre (Flags.only_parse ()) in_file with
    | Some in_sys -> in_sys
    | None -> (
        KEvent.log L_note "No parse errors found!";
        KEvent.terminate_log ();
        exit 0 ) in
  KEvent.log L_info "Lustre program parsed";
  KEvent.log L_debug "%a" LustreNodePrinter.pp_print_subsystems input_system;

  let ns, ps, cs, gs = NodeInstance.translate_subsystems input_system in
  KEvent.log L_info "Node instances generated";
  KEvent.log L_debug "%a@." NodeInstance.pp_print_nodes ns;
  KEvent.log L_debug "%a" NodeInstance.pp_print_props ps;

  KEvent.log L_info "Printing leaf node instances";
  let leaves_ppf = create_ppf Leaves in
  Format.fprintf leaves_ppf "%a" NodeInstanceToLustre.pp_print_nodes ns;
  (*KEvent.log L_debug "%a" NodeInstanceToLustre.pp_print_nodes ns;*)

  KEvent.log L_info "Printing a CHR proof script";
  let cs = CompValidator.translate ns ps cs gs in
  let proof_ppf = create_ppf Proof in
  Format.fprintf proof_ppf "%a" CompValidator.pp_print_script cs;
  (*KEvent.log L_debug "%a" CompValidator.pp_print_script cs;*)

  (*if CompValidator.validate cs then
    Format.printf "valid@."
  else
    Format.printf "invalid@.";
  *)
  KEvent.log L_info "Done";
  ()
with
(* Could not create input system. *)
| LustreAst.Parser_error  ->
   (* We should have printed the appropriate message so just 'gracefully' exit *)
   KEvent.terminate_log () ; exit ExitCodes.error
| LustreInput.NoMainNode msg ->
   KEvent.log L_fatal "Error reading input file '%s': %s" in_file msg ;
   KEvent.terminate_log () ; exit ExitCodes.error
| Sys_error msg ->
   KEvent.log L_fatal "Error opening input file '%s': %s" in_file msg ;
   KEvent.terminate_log () ; exit ExitCodes.error
| e ->
   let backtrace = Printexc.get_raw_backtrace () in
   KEvent.log L_fatal "Unexpected error:@ %s%a"
     (Printexc.to_string e)
     (if Printexc.backtrace_status ()
      then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
      else fun _ _ -> ()) backtrace;
   (* Terminating log and exiting with error. *)
   KEvent.terminate_log () ;
   exit ExitCodes.error  

(* eof *)