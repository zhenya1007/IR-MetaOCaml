(* Copied from meta.ml *)
type closure = unit -> Obj.t
val run_code : string -> closure -> Obj.t
