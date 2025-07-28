open Ast
open Ast_util
open Jib
open Jib_util
open Jib_compile
open Type_check
open Reporting

(* Codal backend configuration *)
let codal_options = []

let codal_rewrites = []

(* Context for Codal compilation *)
type codal_ctx = {
  target_name : string;
  locals : (mut * ctyp) NameMap.t;
  registers : ctyp Bindings.t;
  tc_env : Env.t;
  effect_info : Effects.side_effect_info;
  no_raw : bool;
  no_static : bool;
}

(* Initialize Codal context *)
let init_codal_ctx target_name ast =
  let tc_env = Env.add_typquant (Id_aux (Id "unit", Parse_ast.Unknown)) 
    (TypQ_aux (TypQ_no_forall, Parse_ast.Unknown)) ast.env in
  {
    target_name;
    locals = NameMap.empty;
    registers = Bindings.empty;
    tc_env;
    effect_info = ast.effect_info;
    no_raw = false;
    no_static = false;
  }

(* Convert Jib Types to Codal Types *)
(*There exists 25 types in Jib*)
let rec codal_type_of_ctyp = function
| CT_unit -> 
| CT_bit -> 
| CT_bool -> 
| CT_fbits _ -> 
| CT_sbits _ -> 
| CT_fint _ -> 
| CT_constant _ -> 
| CT_lint -> 
| CT_lbits -> 
| CT_tup _ as tup -> 
| CT_struct (id, _) -> 
| CT_enum id -> 
| CT_variant (id, _) -> 
| CT_list _ as l -> 
| CT_vector _ as v -> 
| CT_fvector (_, typ) -> 
| CT_string ->
| CT_real ->
| CT_json -> 
| CT_json_key -> 
| CT_ref ctyp -> 
| CT_float n -> 
| CT_rounding_mode -> 
| CT_memory_writes ->
| CT_poly _ -> 
(*We have sgen_ctype_name,Used in generated function names, helper macros, and type-based dispatch where the type is part of a name (no *, no C keywords).*)
(*no sgen_const_ctype**)
(*no sgen_mask*)

let sgen_value = function
| VL_bits [] -> 
| VL_bits bs -> 
| VL_int i ->
| VL_bool true -> 
| VL_bool false ->
| VL_unit -> 
| VL_bit Sail2_values.B0 -> 
| VL_bit Sail2_values.B1 -> 
| VL_bit Sail2_values.BU -> 
| VL_real str -> 
| VL_string str -> 
| VL_enum element -> 
| VL_ref r -> 
| VL_undefined -> 



(* Generate Codal value *)
let rec codal_value_of_cval = function
  | V_id (id, ctyp) -> 
      codal_type_of_ctyp ctyp ^ " " ^ string_of_name id
  | V_lit (vl, ctyp) -> 
      codal_literal_of_value vl ctyp
  | V_call (op, cvals) -> 
      codal_operation op cvals
  | V_tuple cvals -> 
      "(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | V_struct (fields, ctyp) -> 
      "{" ^ String.concat ", " (List.map (fun (id, cval) -> 
        "." ^ string_of_id id ^ " = " ^ codal_value_of_cval cval) fields) ^ "}"
  | V_field (cval, id, ctyp) -> 
      codal_value_of_cval cval ^ "." ^ string_of_id id
  | V_ctor_kind (cval, (id, ctyps)) -> 
      codal_value_of_cval cval ^ ".kind == " ^ string_of_id id
  | V_ctor_unwrap (cval, (id, ctyps), ctyp) -> 
      codal_value_of_cval cval ^ "." ^ string_of_id id ^ "_value"
  | V_tuple_member (cval, i, n) -> 
      codal_value_of_cval cval ^ ".f" ^ string_of_int i
  | V_member (id, ctyp) -> 
      string_of_id id
  | V_ref (id, ctyp) -> 
      "&" ^ string_of_id id

(* Convert Sail literals to Codal literals *)
and codal_literal_of_value vl ctyp = match vl with
  | VL_int n -> 
      if Big_int.less_equal (Big_int.of_int (-9223372036854775808)) n &&
         Big_int.less_equal n (Big_int.of_int 9223372036854775807) then
        "INT64_C(" ^ Big_int.to_string n ^ ")"
      else
        "sail_int_of_string(\"" ^ Big_int.to_string n ^ "\")"
  | VL_bool true -> "true"
  | VL_bool false -> "false"
  | VL_bit Sail2_values.B0 -> "false"
  | VL_bit Sail2_values.B1 -> "true"
  | VL_string s -> "\"" ^ String.escaped s ^ "\""
  | VL_unit -> "/* unit */"
  | VL_bits bits -> 
      "sail_bits_of_string(\"" ^ 
      String.concat "" (List.map (function 
        | Sail2_values.B0 -> "0" 
        | Sail2_values.B1 -> "1") bits) ^ "\")"
  | VL_real s -> "sail_real_of_string(\"" ^ s ^ "\")"
  | VL_enum s -> s
  | VL_ref s -> "&" ^ s
  | VL_undefined -> "UNDEFINED(" ^ codal_type_of_ctyp ctyp ^ ")"

(* Convert Sail operations to Codal operations *)
and codal_operation op cvals = match op with
  | Iadd -> 
      "sail_int_add(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Isub -> 
      "sail_int_sub(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Itimes -> 
      "sail_int_mul(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Idiv -> 
      "sail_int_div(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Ilt -> 
      "sail_int_lt(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Ilteq -> 
      "sail_int_lteq(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Igt -> 
      "sail_int_gt(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Igteq -> 
      "sail_int_gteq(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Eq -> 
      "sail_int_eq(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Neq -> 
      "sail_int_neq(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Band -> 
      "(" ^ String.concat " && " (List.map codal_value_of_cval cvals) ^ ")"
  | Bor -> 
      "(" ^ String.concat " || " (List.map codal_value_of_cval cvals) ^ ")"
  | Bnot -> 
      "!(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | Bvadd -> 
      "sail_bits_add(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Bvsub -> 
      "sail_bits_sub(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Bvand -> 
      "sail_bits_and(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Bvor -> 
      "sail_bits_or(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Bvxor -> 
      "sail_bits_xor(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Bvnot -> 
      "sail_bits_not(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | Bvaccess -> 
      "sail_bits_access(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Concat -> 
      "sail_bits_concat(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Zero_extend n -> 
      "sail_bits_zero_extend(" ^ string_of_int n ^ ", " ^ 
      codal_value_of_cval (List.hd cvals) ^ ")"
  | Sign_extend n -> 
      "sail_bits_sign_extend(" ^ string_of_int n ^ ", " ^ 
      codal_value_of_cval (List.hd cvals) ^ ")"
  | Slice n -> 
      "sail_bits_slice(" ^ string_of_int n ^ ", " ^ 
      String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Set_slice -> 
      "sail_bits_set_slice(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | Replicate n -> 
      "sail_bits_replicate(" ^ string_of_int n ^ ", " ^ 
      codal_value_of_cval (List.hd cvals) ^ ")"
  | Index n -> 
      "sail_vector_access(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"
  | List_hd -> 
      "sail_list_hd(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | List_tl -> 
      "sail_list_tl(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | List_is_empty -> 
      "sail_list_is_empty(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | Ite -> 
      let [cond; then_val; else_val] = cvals in
      "(" ^ codal_value_of_cval cond ^ " ? " ^ 
      codal_value_of_cval then_val ^ " : " ^ 
      codal_value_of_cval else_val ^ ")"
  | Get_abstract -> 
      "sail_abstract_get(" ^ codal_value_of_cval (List.hd cvals) ^ ")"
  | String_eq -> 
      "strcmp(" ^ String.concat ", " (List.map codal_value_of_cval cvals) ^ ") == 0"
  | Unsigned n -> 
      "sail_int_unsigned(" ^ string_of_int n ^ ", " ^ 
      codal_value_of_cval (List.hd cvals) ^ ")"
  | Signed n -> 
      "sail_int_signed(" ^ string_of_int n ^ ", " ^ 
      codal_value_of_cval (List.hd cvals) ^ ")"
  | Sslice n -> 
      "sail_bits_sslice(" ^ string_of_int n ^ ", " ^ 
      String.concat ", " (List.map codal_value_of_cval cvals) ^ ")"

(* Generate Codal instruction *)
let rec codal_instr_of_instr ctx = function
  | I_aux (I_decl (ctyp, id), l) -> 
      codal_type_of_ctyp ctyp ^ " " ^ string_of_name id ^ ";\n"
  | I_aux (I_init (ctyp, id, init), l) -> 
      let decl = codal_type_of_ctyp ctyp ^ " " ^ string_of_name id in
      let init_val = match init with
        | Init_cval cval -> " = " ^ codal_value_of_cval cval
        | Init_static vl -> " = " ^ codal_literal_of_value vl ctyp
        | Init_json_key parts -> " = sail_json_key_new(" ^ 
            String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") parts) ^ ")"
      in
      decl ^ init_val ^ ";\n"
  | I_aux (I_copy (clexp, cval), l) -> 
      codal_clexp_of_clexp clexp ^ " = " ^ codal_value_of_cval cval ^ ";\n"
  | I_aux (I_if (cval, then_instrs, else_instrs), l) -> 
      "if (" ^ codal_value_of_cval cval ^ ") {\n" ^
      String.concat "" (List.map (codal_instr_of_instr ctx) then_instrs) ^
      "} else {\n" ^
      String.concat "" (List.map (codal_instr_of_instr ctx) else_instrs) ^
      "}\n"
  | I_aux (I_block instrs, l) -> 
      "{\n" ^ String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "}\n"
  | I_aux (I_funcall (creturn, extern, (id, ctyps), cvals), l) -> 
      let func_name = string_of_id id in
      let args = String.concat ", " (List.map codal_value_of_cval cvals) in
      match creturn with
      | CR_one clexp -> 
          codal_clexp_of_clexp clexp ^ " = " ^ func_name ^ "(" ^ args ^ ");\n"
      | CR_multi clexps -> 
          "sail_multi_return(" ^ func_name ^ ", " ^ args ^ ", " ^
          String.concat ", " (List.map codal_clexp_of_clexp clexps) ^ ");\n"
  | I_aux (I_return cval, l) -> 
      "return " ^ codal_value_of_cval cval ^ ";\n"
  | I_aux (I_clear (ctyp, id), l) -> 
      "sail_clear(" ^ string_of_name id ^ ");\n"
  | I_aux (I_reset (ctyp, id), l) -> 
      "sail_reset(" ^ string_of_name id ^ ");\n"
  | I_aux (I_reinit (ctyp, id, cval), l) -> 
      string_of_name id ^ " = " ^ codal_value_of_cval cval ^ ";\n"
  | I_aux (I_undefined ctyp, l) -> 
      "return UNDEFINED(" ^ codal_type_of_ctyp ctyp ^ ");\n"
  | I_aux (I_exit, l) -> 
      "sail_match_failure(\"" ^ ctx.target_name ^ "\");\n"
  | I_aux (I_comment str, l) -> 
      "// " ^ str ^ "\n"
  | I_aux (I_raw str, l) -> 
      if ctx.no_raw then "" else str ^ "\n"
  | I_aux (I_label str, l) -> 
      str ^ ":\n"
  | I_aux (I_goto str, l) -> 
      "goto " ^ str ^ ";\n"
  | I_aux (I_jump (cval, label), l) -> 
      "if (" ^ codal_value_of_cval cval ^ ") goto " ^ label ^ ";\n"
  | I_aux (I_throw cval, l) -> 
      "sail_throw(" ^ codal_value_of_cval cval ^ ");\n"
  | I_aux (I_try_block instrs, l) -> 
      "try {\n" ^ String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "}\n"
  | I_aux (I_end id, l) -> 
      "// end " ^ string_of_name id ^ "\n"

(* Convert Codal left expression *)
and codal_clexp_of_clexp = function
  | CL_id (id, ctyp) -> 
      string_of_name id
  | CL_rmw (read, write, ctyp) -> 
      string_of_name write
  | CL_field (clexp, id, ctyp) -> 
      codal_clexp_of_clexp clexp ^ "." ^ string_of_id id
  | CL_addr clexp -> 
      "&(" ^ codal_clexp_of_clexp clexp ^ ")"
  | CL_tuple (clexp, n) -> 
      codal_clexp_of_clexp clexp ^ ".f" ^ string_of_int n
  | CL_void ctyp -> 
      "/* void */"

(* Generate Codal function *)
let codal_function_of_cdef ctx = function
  | CDEF_aux (CDEF_fundef (id, heap_return, args, instrs), def_annot) -> 
      let ret_type = match heap_return with
        | Return_plain -> "void"
        | Return_via name -> codal_type_of_ctyp (clexp_ctyp (CL_id (name, CT_unit)))
      in
      let param_list = String.concat ", " (List.map (fun (name, ctyp) -> 
        codal_type_of_ctyp ctyp ^ " " ^ string_of_name name) args) in
      let body = String.concat "" (List.map (codal_instr_of_instr ctx) instrs) in
      ret_type ^ " " ^ string_of_id id ^ "(" ^ param_list ^ ") {\n" ^ body ^ "}\n\n"
  | CDEF_aux (CDEF_register (id, ctyp, instrs), def_annot) -> 
      "// Register " ^ string_of_id id ^ "\n" ^
      codal_type_of_ctyp ctyp ^ " " ^ string_of_name id ^ ";\n" ^
      String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "\n"
  | CDEF_aux (CDEF_val (id, tyvars, ctyps, ctyp, extern), def_annot) -> 
      let param_types = String.concat ", " (List.map codal_type_of_ctyp ctyps) in
      let extern_str = match extern with
        | Some extern_name -> " = " ^ extern_name
        | None -> ""
      in
      codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ 
      "(" ^ param_types ^ ")" ^ extern_str ^ ";\n"
  | CDEF_aux (CDEF_type ctype_def, def_annot) -> 
      codal_type_def_of_ctype_def ctype_def
  | CDEF_aux (CDEF_let (n, bindings, instrs), def_annot) -> 
      "// Let binding " ^ string_of_int n ^ "\n" ^
      String.concat "" (List.map (fun (id, ctyp) -> 
        codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ ";\n") bindings) ^
      String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "\n"
  | CDEF_aux (CDEF_startup (id, instrs), def_annot) -> 
      "void " ^ string_of_id id ^ "_startup() {\n" ^
      String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "}\n\n"
  | CDEF_aux (CDEF_finish (id, instrs), def_annot) -> 
      "void " ^ string_of_id id ^ "_finish() {\n" ^
      String.concat "" (List.map (codal_instr_of_instr ctx) instrs) ^ "}\n\n"
  | CDEF_aux (CDEF_pragma (name, str), def_annot) -> 
      "// #pragma " ^ name ^ " " ^ str ^ "\n"

(* Generate Codal type definition *)
and codal_type_def_of_ctype_def = function
  | CTD_aux (CTD_enum (id, members), def_annot) -> 
      "enum " ^ string_of_id id ^ " {\n" ^
      String.concat ",\n" (List.map string_of_id members) ^ "\n};\n\n"
  | CTD_aux (CTD_struct (id, tyvars, fields), def_annot) -> 
      "struct " ^ string_of_id id ^ " {\n" ^
      String.concat "" (List.map (fun (id, ctyp) -> 
        "  " ^ codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ ";\n") fields) ^
      "};\n\n"
  | CTD_aux (CTD_variant (id, tyvars, ctors), def_annot) -> 
      "union " ^ string_of_id id ^ " {\n" ^
      String.concat "" (List.map (fun (id, ctyp) -> 
        "  " ^ codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ "_value;\n") ctors) ^
      "};\n\n"
  | CTD_aux (CTD_abbrev (id, ctyp), def_annot) -> 
      "typedef " ^ codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ ";\n\n"
  | CTD_aux (CTD_abstract (id, ctyp, init), def_annot) -> 
      "typedef " ^ codal_type_of_ctyp ctyp ^ " " ^ string_of_id id ^ ";\n\n"

let rec ctyp_dependencies = function(*2264 we need this*)
let codegen_ctg ctx = function (*2266 we need this*)
let codegen_def ctx def=  (*2291*)(*It converts one jib definition to list of Document.t values*)
    let ctyps = cdef_ctyps def |> CTSet.elements in
    (*cdef_ctyps is a function that returns a set of ctyps for a given jib definition*)
    (*CTSet.elements converts the set to a list*)
    if List.exists is_polymorphic ctyps then (
(*Checks if any of the types used are polymorphic (i.e., contain type variables like 'a, 'b, etc.).
These should have been resolved (monomorphized) before code generation.*)
    let polymorphic_ctyps = List.filter is_polymorphic ctyps in
    c_error
      (Printf.sprintf "Found polymorphic types:\n%s\nwhile generating definition."
         (Util.string_of_list "\n" string_of_ctyp polymorphic_ctyps)
      )
  ) (*Filters to only keep the polymorphic types.  *)
  else (
    let deps = List.concat (List.map ctyp_dependencies ctyps) in
   (* For each used type in ctyps, compute its dependencies (i.e., other types it refers to).
    ctyp_dependencies: probably returns a list of dependent ctyps for each one.
    Flatten all dependency lists with List.concat.*)

    List.concat (List.map (codegen_ctg ctx) deps) @ codegen_def' ctx def
   (* Calls codegen_ctg for each dependency in deps to generate code for them.
codegen_ctg might generate typedefs, enums, etc.
    
    Uses ctx to track context/config.*)
(*So inside every jib definition there is a hidden C?
Also when we turn compile_ast do we use AST or anf
*)  
  
    )



module C_config (Opts : sig
(*We need module C_config type conding*)
(*Its main job is to define how 
Sail types map to C types in the JIB compiler backend.*)
(*Does this embed Ctype into AST while creating Jib?*)
let jib_of_ast env effect_info ast =
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
    end)) in
    let ctx = initial_ctx env effect_info in
    Jibc.compile_ast ctx ast      

let compile_ast env effet_info basename ast =
try
    (*Returns header: string option and impl: string*)
    (*228 line but we will ignore
-No insert_heap_returns 
-No recursive_functions find onlining optimiting
-No optimize
-No flatten_cdef not flattens nested more than 100 that is for clang
-No coverage_include, coverage_hook_header
-No no_coverage_hook
-No code preamble generates RTS,Sail,configired user header
-No coverage setup and .h and .c seperation
-No exception handling
-No let-binding and startup code
-No register initialization
--No runtime lifecycle functions
-model_init
-model_fini
-model_pre_exit
.model_main should be reduced in here
-No unit test supports
-No model_test
*)
let cdefs, ctx = jib_of_ast env effect_info ast in
(*Converting ast to jib, cdefs is code and ctx is context
what context means and why necessary?
*)
let header_doc_opt, docs = List.map (codegen_def ctx) cdefs |> List.concat |> merge_file_docs in
(*List.map mapping the function (codegen_def ctx) to the list cdefs
cdefs are list of core language definitions in jib that will be compiled into C
So codefen function compiles one definition to list of Document.t valies
pretty print chuncks of C code
1,Step: code_docs: Document.t list list where each inner list is the
C Code for a single Sail definition
2.Flattens the list so it is just Document.t list a flat list of all generated
C code blocks
3.This is a helper function that takes a list of code "documents" (Document.t list) and:
Splits them into two groups:
Header content: declarations that go into a .h file (e.g., prototypes, extern declarations, #defines, type aliases).
Implementation content: function definitions, global variables, etc. that go into the .c file.


*)


(*
-What is codegen_def for
-merge_file_docs
-doc: Output c document
- header_doc_opt:optinonal header file doc we dont have
-No header
-No error handling
*)


let model_main =
    [
      Printf.sprintf "%sint model_main(int argc, char *argv[])" (static ());
      "{";
      "  model_init();";
      "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
      Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "main"));
      "  model_fini();";
      "  model_pre_exit();";
      "  return EXIT_SUCCESS;";
      "}";
    ]
    |> List.map string |> separate hardline
  in


  let actual_main =
    let extra_pre =
      List.filter_map
        (function CDEF_aux (CDEF_pragma ("c_in_main", arg), _) -> Some ("  " ^ arg) | _ -> None)
        cdefs
    in
    let extra_post =
      List.filter_map
        (function CDEF_aux (CDEF_pragma ("c_in_main_post", arg), _) -> Some ("  " ^ arg) | _ -> None)
        cdefs
    in
    separate hardline
      ( if Config.no_main then []
        else
          List.map string
            (["int main(int argc, char *argv[])"; "{"; "  int retcode;"]
            @ extra_pre @ ["  retcode = model_main(argc, argv);"] @ extra_post @ ["  return retcode;"; "}"]
            )
      )
  in

  let header =
    Option.map
      (fun header ->
        string "#pragma once" ^^ hlhl ^^ preamble true ^^ hlhl ^^ header ^^ hardline ^^ end_extern_cpp ^^ hardline
        |> Document.to_string
      )
      header_doc_opt
  in (*header is the first element of the return tuple*)
  ( header,
    Document.to_string
      (preamble false
      ^^ (if Config.generate_header then hardline ^^ Printf.ksprintf string "#include \"%s.h\"" basename else empty)
      ^^ hlhl ^^ docs ^^ hlhl
      ^^ ( if not Config.no_rts then
             model_init ^^ hlhl ^^ model_fini ^^ hlhl ^^ model_pre_exit ^^ hlhl ^^ model_main ^^ hlhl
           else empty
         )
      ^^ unit_test_defs ^^ hlhl ^^ model_test ^^ hlhl ^^ actual_main ^^ hardline ^^ end_extern_cpp ^^ hardline
      )
  )
        

(* Main Codal emission function 
let emit_codal (ast : Type_check.typed_ast) filename =
  let ctx = init_codal_ctx "codal" ast in
  
  (* Compile to Jib IR *)
  let jib_ast = compile_ast ctx ast in
  
  (* Generate Codal code *)
  let codal_code = 
    "// Codal backend output\n" ^
    "// Generated from Sail AST\n\n" ^
    "#include <stdint.h>\n" ^
    "#include <stdbool.h>\n" ^
    "#include <string.h>\n" ^
    "#include \"sail.h\"\n\n" ^
    String.concat "" (List.map (codal_function_of_cdef ctx) jib_ast)
  in
  
  (* Write to file *)
  let oc = open_out filename in
  output_string oc codal_code;
  close_out oc

(* Codal target registration *)
let codal_target = {
  Target.name = "codal";
  Target.options = codal_options;
  Target.rewrites = codal_rewrites;
  Target.supports_abstract_types = true;
  Target.supports_runtime_config = true;
  Target.emit = emit_codal;
} 
end  