open Format

(* Copied from meta.ml (the declaration for reify_code), and modified *)
type closure = unit -> Obj.t (* FIXME: I am pretty sure that, on this side of the Atlantic, they call such a thing "a thunk" *)
external replace_code: string -> int -> closure -> closure = "metaocaml_replace_code"

type evaluation_outcome = Result of Obj.t | Exception of exn

(* Copied from toploop.ml, and then modified
   The problem with the original is that it calls Bytegen.compile_phrase
   which compiles the lambda-form passed to it in an empty environment.
   However, compiling the form in an empty environment is at odds with
   cross-stage persistance. *)
let load_lambda ppf lam env clos =
  if !Clflags.dump_rawlambda then fprintf ppf "%a@." Printlambda.lambda lam;
  let slam = Simplif.simplify_lambda lam in
  if !Clflags.dump_lambda then fprintf ppf "%a@." Printlambda.lambda slam;
  let (init_code, fun_code) = Bytegen.compile_for_metaocaml slam env in
  if !Clflags.dump_instr then
    fprintf ppf "%a%a@."
    Printinstr.instrlist init_code
    Printinstr.instrlist fun_code;
  let (code, code_size, reloc) = Emitcode.to_memory init_code fun_code in
  let can_free = (fun_code = []) in
  let initial_symtable = Symtable.current_state() in
  Symtable.patch_object code reloc;
  Symtable.check_global_initialized reloc;
  Symtable.update_global_table();
  try
    let retval = (replace_code code code_size clos) () in
    if can_free then begin
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    end;
    Result retval
  with x ->
    if can_free then begin
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    end;
    Symtable.restore_state initial_symtable;
    Exception x

let run_code s clos =
  let (env, lam) = (Marshal.from_string s 0 : Instruct.compilation_env * Lambda.lambda) in
  (* FIXME: always passing Format.std_formatter here is a kludge *)
  match load_lambda Format.std_formatter lam env clos with
  | Result v -> v
  | Exception x -> raise x

let () = Callback.register "Metaocaml.run_code" run_code
