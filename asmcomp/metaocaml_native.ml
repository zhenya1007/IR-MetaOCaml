open Config

(* copied from Opttoploop.load_lambda, and modified *)
let load_ulambda ppf (size, ulam) =

  let unit_name = Compilenv.current_unit_name () in
  let dll =
    if !Clflags.keep_asm_file then "caml" ^ unit_name ^ ext_dll
    else Filename.temp_file ("caml" ^ unit_name) ext_dll
  in
  let fn = Filename.chop_extension dll in
  Asmgen.compile_for_metaocaml ~toplevel:Opttoploop.need_symbol fn ppf (size, ulam);
  Asmlink.call_linker_shared [fn ^ ext_obj] dll;
  Sys.remove (fn ^ ext_obj);

  let dll =
    if Filename.is_implicit dll
    then Filename.concat (Sys.getcwd ()) dll
    else dll in
  let res = Opttoploop.dll_run dll unit_name in
  (try Sys.remove dll with Sys_error _ -> ());
  (* note: under windows, cannot remove a loaded dll
     (should remember the handles, close them in at_exit, and then remove
     files) *)
  res


let run_code s =
  let dcmm = !Clflags.dump_cmm in
  let ulam = (Marshal.from_string s 0 : Clambda.ulambda) in
  try
    (* FIXME: always passing Format.std_formatter here is a kludge *)

    (* [size] below refers to "the size of the global block", i.e.,
    where module-global variables are stored; since we are not storing
    module-global variables, size is zero *)

    Clflags.dump_cmm := true;
    let r =
      match load_ulambda Format.std_formatter (0,ulam) with
      | Opttoploop.Result v -> v
      | Opttoploop.Exception x -> raise x
    in
    Clflags.dump_cmm := dcmm;
    r
  with x ->
    Clflags.dump_cmm := dcmm;
    raise x

let _ = Callback.register "Metaocaml.run_code" run_code;
