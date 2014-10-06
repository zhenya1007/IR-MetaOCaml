open Format

(* Copied from meta.ml (the declaration for reify_code), and modified *)
external prepare_bytecode: bytes -> int ->  unit = "metaocaml_prepare_bytecode"

type evaluation_outcome = Result of Obj.t | Exception of exn

(* Copied from toploop.ml, and then modified
   The problem with the original is that it calls Bytegen.compile_phrase
   which compiles the lambda-form passed to it in an empty environment.
   However, compiling the form in an empty environment is at odds with
   cross-stage persistence. *)
let load_lambda ppf lam comp_env val_env =
  let set_code_pointer clos code = 
    Obj.set_field clos 0 code in
  if !Clflags.dump_rawlambda then fprintf ppf "%a@." Printlambda.lambda lam;
  let slam = Simplif.simplify_lambda lam in
  if !Clflags.dump_lambda then fprintf ppf "%a@." Printlambda.lambda slam;
  let (init_code, fun_code) = Bytegen.compile_for_metaocaml slam comp_env in
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
    let clos = Obj.dup val_env in
    prepare_bytecode code code_size;
    set_code_pointer clos (Obj.magic code);
    let f : unit -> Obj.t = Obj.magic clos in
    let retval = f () in
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

let run_code block =
  let (s, val_env) = (Obj.magic (Obj.field block 0), Obj.field block 1) in
  let (comp_env, lam) = (Marshal.from_string s 0 : Instruct.compilation_env * Lambda.lambda) in
  (* FIXME: always passing Format.std_formatter here is a kludge *)
  match load_lambda std_formatter lam comp_env val_env with
  | Result v -> v
  | Exception x -> raise x

let () = Callback.register "Metaocaml.run_code" run_code
