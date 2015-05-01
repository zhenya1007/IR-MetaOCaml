let run_code block =
  let s = Obj.obj (Obj.field block (Obj.size block - 1)) in
  let lc = (Marshal.from_string s 0 : Lambda.code_description) in
  let lc' = {lc with Lambda.lc_block = block} in
  match Opttoploop.load_lambda Format.std_formatter (0, Lambda.Lrun lc') with
    | Opttoploop.Result v -> v
    | Opttoploop.Exception x -> raise x
  (* FIXME: always passing Format.std_formatter here is a kludge *)

  (* [size] above refers to "the size of the global block", i.e.,
  where module-global variables are stored; since we are not storing
  module-global variables, size is zero *)

let process_code block =
  let s = Obj.obj (Obj.field block (Obj.size block - 1)) in
  let lc = (Marshal.from_string s 0 : Lambda.code_description) in
  let lc' = {lc with Lambda.lc_block = block} in
  match Opttoploop.load_lambda Format.std_formatter (0, Lambda.Lrun lc') with
    | Opttoploop.Result v -> v
    | Opttoploop.Exception x -> raise x
  (* FIXME: always passing Format.std_formatter here is a kludge *)

  (* [size] above refers to "the size of the global block", i.e.,
  where module-global variables are stored; since we are not storing
  module-global variables, size is zero *)

let () = Callback.register "Metaocaml.run_code" run_code
let () = Callback.register "Metaocaml.process_code" process_code
