open Ast
open Ast_util
open Jib
open Jib_util
open Jib_compile
open Type_check
open Reporting

(* Codal backend configuration *)
(* Context for Codal compilation *)
(* Initialize Codal context *)

(**************************************************************************)
(* NO 2. Converting sail types to C types   - Only moduleC       LLIne:86                           *)
(**************************************************************************)


  module C_config (Opts : sig
    (*We need module C_config type conding*)
    (*Its main job is to define how 
    Sail types map to C types in the JIB compiler backend.*)


(**************************************************************************)
(* NO 3. Optimization of primitives and literals   line.294                          *)
(**************************************************************************)

(**************************************************************************)
(* NO 5. Optimizations       lINE:634                                               *)
(**************************************************************************)

(**************************************************************************)
(* 6. Code generation     LINE:920                                                *)
(**************************************************************************)

(* Line:993
-sgen_id
-sgen_uid
-sgen_name 
-codegen_id depends sgen_id 
-sgen_function_id 
-sgen_function_uid depends sgen_uid 
-codegen_function_id  depends sgen_function_id 
*)

(* Convert Jib Types to Codal Types *)
(*There exists 25 types in Jib*)
let rec sgen_ctyp = function (*depends sgen_id,sgen_ctyp*)
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
(*-sgen_const_ctype dep sgen_ctype**)
(*-sgen_mask*)

let sgen_value = function (*dep sgen_id*)
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

(*-sgen_tuple_id dep sgen_id*)
(*sgen_cval are value constructors dep sgen_name,sgen_id,sgen_value,sgen_call,sgen_cval,sgen_tuple_id,sgen_uid*)
let rec sgen_cval = function
| V_id (id, _) -> 
| V_member (id, _) -> 
| V_lit (vl, _) -> 
| V_call (op, cvals) -> 
| V_field (f, field, _) -> 
| V_tuple_member (f, _, n) -> 
| V_ctor_kind (f, ctor) -> 
| V_struct (fields, _) ->
| V_ctor_unwrap (f, ctor, _) -> 
| V_tuple _ -> 

(*These are operator arithmetic, logical, it prints in C format in c bakcned**)
and sgen_call op cvals = (*sgen_cval, cval_ctyp*)
     match (op, cvals) with
    | Bnot, [v] -> 
    | Band, vs ->
    | Bor, vs -> 
    | List_hd, [v] -> 
    | List_tl, [v] ->
    | List_is_empty, [v] -> 
    | Eq, [v1; v2] -> begin
    | Neq, [v1; v2] -> begin
    | Ilt, [v1; v2] -> 
    | Igt, [v1; v2] -> 
    | Ilteq, [v1; v2] -> 
    | Igteq, [v1; v2] -> 
    | Iadd, [v1; v2] -> 
    | Isub, [v1; v2] -> 
    | Unsigned 64, [vec] -> 
    | Signed 64, [vec] ->
    | Bvand, [v1; v2] -> begin
    | Bvnot, [v] -> begin
    | Bvor, [v1; v2] -> begin
    | Bvxor, [v1; v2] -> begin
    | Bvadd, [v1; v2] -> begin
    | Bvsub, [v1; v2] -> begin
    | Bvaccess, [vec; n] -> begin
    | Slice len, [vec; start] -> begin
    | Sslice 64, [vec; start; len] -> begin
    | Set_slice, [vec; start; slice] -> begin
    | Zero_extend n, [v] -> begin
    | Sign_extend n, [v] -> begin
    | Replicate n, [v] -> begin
    | Concat, [v1; v2] -> begin
    | Get_abstract, [v] -> 
    | Ite, [i; t; e] -> 
    | String_eq, [s1; s2] -> 
    | _, _ -> 
    

(*generating the parameter string for function calls, depending on the compile-time type of the value *)
      let sgen_cval_param cval = (*depends sgen_cval*)
        | CT_lbits -> 
        | CT_sbits _ -> 
        | CT_fbits len -> 
        | _ ->
(* C backend l-expression (l-value) generator — it translates jib clexp patterns into the C code that points to or dereferences the right variable or struct field.*)
      let rec sgen_clexp l = function (*sgen_name,sgen_clexp,sgen_id,sgen_tuple_id*)
        | CL_id (Have_exception _, _) -> 
        | CL_id (Current_exception _, _) ->
        | CL_id (Throw_location _, _) ->
        | CL_id (Memory_writes _, _) -> 
        | CL_id (Channel _, _) -> 
        | CL_id (Return _, _) -> 
        | CL_id (name, _) -> 
        | CL_field (clexp, field, _) -> 
        | CL_tuple (clexp, n) -> 
        | CL_addr clexp ->
        | CL_void _ -> 
        | CL_rmw _ ->
(*It generates the C expression corresponding to a left expression (clexp), but as a value, not as a pointer.*)
      let rec sgen_clexp_pure l = function
        | CL_id (Have_exception _, _) -> 
        | CL_id (Current_exception _, _) -> 
        | CL_id (Throw_location _, _) -> 
        | CL_id (Memory_writes _, _) -> 
        | CL_id (Channel _, _) -> 
        | CL_id (Return _, _) -> 
        | CL_id (name, _) -> 
        | CL_field (clexp, field, _) -> 
        | CL_tuple (clexp, n) -> 
        | CL_addr clexp -> 
        | CL_void _ -> 
        | CL_rmw _ -> 
      (** Generate instructions to copy from a cval to a clexp. This will insert any needed type conversions from big
          integers to small integers (or vice versa), or from arbitrary-length bitvectors to and from uint64 bitvectors as
          needed. *)

    (*Generates C code to copy a value (cval) into a location (clexp).

Handles type conversions if the source and target types differ (e.g., big integer ↔ small integer, variable-length vector ↔ fixed 64-bit vector, tuple types, etc.).*)
      let rec codegen_conversion l ctx clexp cval = (*depends is_stack_ctyp,sgen_clexp_,sgen_clexp_pure,clexp,sgen_cval*)
        (* When both types are equal, we don't need any conversion. *)
        | _, _ when ctyp_equal ctyp_to ctyp_from -> (*dep sgne_ctype_name*)
        | CT_ref _, _ -> c
        | ( (CT_vector ctyp_elem_to | CT_fvector (_, ctyp_elem_to)),
            (CT_vector ctyp_elem_from | CT_fvector (_, ctyp_elem_from)) ) -> (*dep ngensym,sail_kill*)
        (*vector to vector conversion up*)
        (* If we have to convert between tuple types, convert the fields individually. *)
        | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
        (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
        | _, _ when is_stack_ctyp ctx (clexp_ctyp clexp) ->
            (*sail_convert_of*)
        | _, _ ->
(*codegen_conversion;Correct type-safe assignment in generated C code.,Calls appropriate create/copy/kill helpers for heap-managed types.
Recursively handles nested structures (vectors, tuples).*)
    
(*-squash_empty
-sq_separate_map*)


let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
    match instr with
    | I_decl (ctyp, id) when is_stack_ctyp ctx ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
    | I_decl (ctyp, id) ->
        ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        ^^ hardline
        ^^ sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval
    | I_jump (cval, label) -> ksprintf string "  if (%s) goto %s;" (sgen_cval cval) label
    | I_if (cval, [], else_instrs) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [])
    | I_if (cval, [then_instr], []) ->
        ksprintf string "  if (%s)" (sgen_cval cval)
        ^^ space
        ^^ surround 2 0 lbrace (codegen_instr fid ctx then_instr) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, []) ->
        string "  if" ^^ space
        ^^ parens (string (sgen_cval cval))
        ^^ space
        ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, else_instrs) ->
        let rec codegen_if cval then_instrs else_instrs =
          match else_instrs with
          | [I_aux (I_if (else_i, else_t, else_e), _)] ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space ^^ codegen_if else_i else_t else_e
          | _ ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) else_instrs)
                   (twice space ^^ rbrace)
        in
        twice space ^^ codegen_if cval then_instrs else_instrs
    | I_block instrs ->
        string "  {" ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline ^^ string "  }"
    | I_try_block instrs ->
        string "  { /* try */"
        ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs)
        ^^ hardline ^^ string "  }"
    | I_funcall (x, special_extern, f, args) ->
        let x =
          match x with
          | CR_one x -> x
          | CR_multi _ -> Reporting.unreachable l __POS__ "Multiple returns should not exist in C backend"
        in
        let c_args = Util.string_of_list ", " sgen_cval args in
        let ctyp = clexp_ctyp x in
        let is_extern = ctx_is_extern (fst f) ctx || special_extern in
        let fname =
          if special_extern then string_of_id (fst f)
          else if ctx_is_extern (fst f) ctx then ctx_get_extern (fst f) ctx
          else sgen_function_uid f
        in
        let fname =
          match (fname, ctyp) with
          | "internal_pick", _ -> sprintf "pick_%s" (sgen_ctyp_name ctyp)
          | "sail_cons", _ -> begin
              match Option.map cval_ctyp (List.nth_opt args 0) with
              | Some ctyp -> Util.zencode_string ("cons#" ^ string_of_ctyp (ctyp_suprema ctyp))
              | None -> c_error "cons without specified type"
            end
          | "eq_anything", _ -> begin
              match args with
              | cval :: _ -> sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "eq_anything function with bad arity."
            end
          | "length", _ -> begin
              match args with
              | cval :: _ -> sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "length function with bad arity."
            end
          | "vector_access", CT_bit -> "bitvector_access"
          | "vector_access_inc", CT_bit -> "bitvector_access_inc"
          | "vector_access", _ -> begin
              match args with
              | cval :: _ -> sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "vector access function with bad arity."
            end
          | "vector_init", _ -> sprintf "vector_init_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange", _ -> sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange_inc", _ -> sprintf "vector_update_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange", _ -> sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange_inc", _ -> sprintf "vector_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_update", CT_fbits _ -> "update_fbits"
          | "vector_update", CT_lbits -> "update_lbits"
          | "vector_update", _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
          | "vector_update_inc", CT_fbits _ -> "update_fbits_inc"
          | "vector_update_inc", CT_lbits -> "update_lbits_inc"
          | "string_of_bits", _ -> begin
              match cval_ctyp (List.nth args 0) with
              | CT_fbits _ -> "string_of_fbits"
              | CT_lbits -> "string_of_lbits"
              | _ -> assert false
            end
          | "decimal_string_of_bits", _ -> begin
              match cval_ctyp (List.nth args 0) with
              | CT_fbits _ -> "decimal_string_of_fbits"
              | CT_lbits -> "decimal_string_of_lbits"
              | _ -> assert false
            end
          | "internal_vector_update", _ -> sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
          | "internal_vector_init", _ -> sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
          | "undefined_bitvector", CT_fbits _ -> "UNDEFINED(fbits)"
          | "undefined_bitvector", CT_lbits -> "UNDEFINED(lbits)"
          | "undefined_bit", _ -> "UNDEFINED(fbits)"
          | "undefined_vector", _ -> sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
          | "undefined_list", _ -> sprintf "UNDEFINED(%s)" (sgen_ctyp_name ctyp)
          | fname, _ -> fname
        in
        if fname = "reg_deref" then
          if is_stack_ctyp ctx ctyp then ksprintf string "  %s = *(%s);" (sgen_clexp_pure l x) c_args
          else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s, *(%s)" (sgen_clexp_pure l x) c_args
        else if is_stack_ctyp ctx ctyp then
          string (Printf.sprintf "  %s = %s(%s%s);" (sgen_clexp_pure l x) fname (extra_arguments is_extern) c_args)
        else string (Printf.sprintf "  %s(%s%s, %s);" fname (extra_arguments is_extern) (sgen_clexp l x) c_args)
    | I_clear (ctyp, _) when is_stack_ctyp ctx ctyp -> empty
    | I_clear (ctyp, id) -> sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_init (ctyp, id, init) -> (
        match init with
        | Init_cval cval ->
            codegen_instr fid ctx (idecl l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
        | Init_static VL_undefined -> ksprintf string "  static %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        | Init_static vl -> ksprintf string "  static %s %s = %s;" (sgen_ctyp ctyp) (sgen_name id) (sgen_value vl)
        | Init_json_key parts ->
            ksprintf string "  sail_config_key %s = {%s};" (sgen_name id)
              (Util.string_of_list ", " (fun part -> "\"" ^ part ^ "\"") parts)
      )
    | I_reinit (ctyp, id, cval) ->
        codegen_instr fid ctx (ireset l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
    | I_reset (ctyp, id) when is_stack_ctyp ctx ctyp ->
        string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | I_reset (ctyp, id) -> sail_recreate ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_return cval -> twice space ^^ c_return (string (sgen_cval cval))
    | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
    | I_undefined ctyp ->
        let rec codegen_exn_return ctyp =
          match ctyp with
          | CT_unit -> ("UNIT", [])
          | CT_bit -> ("UINT64_C(0)", [])
          | CT_fint _ -> ("INT64_C(0xdeadc0de)", [])
          | CT_lint when !optimize_fixed_int -> ("((sail_int) 0xdeadc0de)", [])
          | CT_fbits _ -> ("UINT64_C(0xdeadc0de)", [])
          | CT_sbits _ -> ("undefined_sbits()", [])
          | CT_lbits when !optimize_fixed_bits -> ("undefined_lbits(false)", [])
          | CT_bool -> ("false", [])
          | CT_enum _ -> (sprintf "((%s)0)" (sgen_ctyp ctyp), [])
          | CT_tup ctyps when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              let fold (n, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_tuple_id n) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold (List.mapi (fun i x -> (i, x)) ctyps) ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                  ^ Util.string_of_list ", " (fun x -> x) inits
                  ^ " };";
                ]
                @ prev
              )
          | CT_struct _ when is_stack_ctyp ctx ctyp ->
              let fields = struct_field_bindings l ctx ctyp |> snd |> Bindings.bindings in
              let gs = ngensym () in
              let fold (id, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_id id) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold fields ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                  ^ Util.string_of_list ", " (fun x -> x) inits
                  ^ " };";
                ]
                @ prev
              )
          | CT_ref _ -> ("NULL", [])
          | ctyp -> c_error ("Cannot create undefined value for type: " ^ string_of_ctyp ctyp)
        in
        let ret, prev = codegen_exn_return ctyp in
        separate_map hardline (fun str -> string ("  " ^ str)) (List.rev prev)
        ^^ hardline
        ^^ string (Printf.sprintf "  return %s;" ret)
    | I_comment str -> string ("  /* " ^ str ^ " */")
    | I_label str -> string (str ^ ": ;")
    | I_goto str -> string (Printf.sprintf "  goto %s;" str)
    | I_raw _ when ctx.no_raw -> empty
    | I_raw str -> string ("  " ^ str)
    | I_end _ -> assert false
    | I_exit _ -> string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")


(*1560
-codegen_type_def 
- generated
-codegen_tup
-codegen_list
-codegen_vector   
-is_decl
-codegen_decl
-codegen_alloc
-codegen_def' 
-c_gen_typ  
-ctyp_dependencies (*2264 we need this*)
-codegen_ctg (*2266 we need this*)
-merge_file_docs
2287*)

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

(*2306
-is_cdef_startup
-sgen_startup
-sgen_instr 
-is_cdef_finish
-sgen_finish
-get_recursive_functions
2325*)


(*Does this embed Ctype into AST while creating Jib?*)
let jib_of_ast env effect_info ast =
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
    end)) in
    let ctx = initial_ctx env effect_info in
    Jibc.compile_ast ctx ast      

(*2336
-c_ast_registers
-get_unit_tests
2351*)


(*2353**)
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
        
        end