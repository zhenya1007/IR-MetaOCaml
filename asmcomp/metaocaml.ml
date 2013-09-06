let run_code s =
  let lam = (Marshal.from_string s 0 : Lambda.lambda) in
  (* FIXME: always passing Format.std_formatter here is a kludge *)
  (* FIXME: passing in 0 for size below is a kludge *)
  match Opttoploop.load_lambda Format.std_formatter (0,lam) with
  | Opttoploop.Result v -> v
  | Opttoploop.Exception x -> raise x

let _ = Callback.register "Metaocaml.run_code" run_code
