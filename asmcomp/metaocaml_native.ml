let run_code block =
  let s = Obj.obj (Obj.field block (Obj.size block - 1)) in
  let lc = (Marshal.from_string s 0 : Lambda.code_description) in
  let lc' = {lc with Lambda.lc_block = Some block} in
  (* any splices should have been already processed by rebuild *)
  if lc.Lambda.lc_splices_count <> 0 then failwith "metaocaml_native(run_code_block)";
  match Opttoploop.load_lambda Format.std_formatter (0, Lambda.Lrun lc') with
    | Opttoploop.Result v -> v
    | Opttoploop.Exception x -> raise x
  (* FIXME: always passing Format.std_formatter here is a kludge *)

  (* [size] above refers to "the size of the global block", i.e.,
  where module-global variables are stored; since we are not storing
     module-global variables, size is zero *)

(* analogous to the function [last] in Lisp *)
let last_field block n =
  Obj.obj (Obj.field block (Obj.size block - n))

let rec code_description_of_block block =
  let s = last_field block 1 in
  let lc = (Marshal.from_string s 0 : Lambda.code_description) in
  update_lc lc block

and update_lc lc block =
  let rec loop n lst =
    if n = lc.Lambda.lc_splices_count then lst
    else
      let lc' = code_description_of_block (last_field block (n+2)) in
      loop (n+1) (lc'::lst)
  in
  {lc with Lambda.lc_block = Some block;
           lc_splices = loop 0 []}

let process_code block =
  let lc = code_description_of_block block in
  let rb = Lambda.Lrebuild lc in
  if !Clflags.dump_rawlambda then
    Format.eprintf "@[process_block %a@]@." Printlambda.lambda rb;
  match Opttoploop.load_lambda Format.std_formatter (0, rb) with
    | Opttoploop.Result v -> v
    | Opttoploop.Exception x -> raise x
  (* FIXME: always passing Format.std_formatter here is a kludge *)

  (* [size] above refers to "the size of the global block", i.e.,
  where module-global variables are stored; since we are not storing
     module-global variables, size is zero *)


let () = Callback.register "Metaocaml.run_code" run_code
let () = Callback.register "Metaocaml.process_code" process_code
