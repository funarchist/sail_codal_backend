(* Minimal plugin registration for Codal backend *)
open Libsail

open Ast_util
open Interactive.State

(*I give no options so no need to define 
-opt_ vars, 
-codal_options
-codal_rewrites, 
-collect_codal_name_info
-no header part
-No reference to any of this in target deceleration
-NO building option
-No if not output file name put into echo
-No check for reserve or overrides names

*)  



let codal_target out_file { ast; effect_info; env; default_sail_dir; _ }=
(* ast: the Sail AST to be compiled., where it comes from?
effect_info: information about side effects in the Sail program.
env: ?
default_sail_dir: default Sail directory.
*)

  let basename = Filename.basename out_file in
(*std Filename folder which is used in compile_ast*)
  Reporting.opt_warnings := true;
  (*Turns on compiler warnings*)
  let echo_output, out_file = match out_file with Some f -> (false, f) | None -> (true, "out") in
   (*Checks whether in CLI output file name provided if not gives name out, if yes takes provided name no cli message*)


  let header_opt, impl = Codalgen.compile_ast env effect_info basename ast in


(* In here output of the compile ast is C code as generated string it is put into
impl(implementation) and we can create header optionally but not in this case *)
  (*Is ast->anf->jib transform happening in compile_Ast?*)
  let impl_out = Util.open_output_with_check (out_file ^ ".c") in
  (*We create name  of the file that string will be printed in*)
  output_string impl_out.channel impl;
  (*stdlib/Outchannel.output_string Write the string on the given output channel.*)
  flush impl_out.channel;
  (*Outchannel.flush flushes the output channel. *)

  (*Is generated codal code can be built?*)

  let () =
  Target.register ~name:"codal" codal_target 