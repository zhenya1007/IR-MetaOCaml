let run_code s =
  let lam = (Marshal.from_string s 0 : Lambda.lambda) in
  (* FIXME: always passing Format.std_formatter here is a kludge *)
  match Toploop.load_lambda Format.std_formatter lam with
  | Toploop.Result v -> v
  | Toploop.Exception x -> raise x

let _ = Callback.register "Metaocaml.run_code" run_code
