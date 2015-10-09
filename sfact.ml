(*The peval2 interpreter from Taha's Gentle Introduction to MSP 1*)
type exp = Int of int | Var of string | App of string * exp
           | Add of exp * exp | Sub of exp * exp
           | Mul of exp * exp | Div of exp * exp | Ifz of exp * exp * exp

type def = Declaration of string * string * exp
type prog = Program of def list * exp

let fact = Program ([Declaration
		       ("fact","x", Ifz(Var "x",
					Int 1,
					Mul(Var"x",
					    (App ("fact", Sub(Var "x",Int 1))))))
		   ],
		    App ("fact", Int 0))

exception Yikes

(* env0, fenv : ’a -> ’b *)
let env0 = fun _ -> raise Yikes 
let fenv0 = env0

(* ext : (’a -> ’b) -> ’a -> ’b -> ’a -> ’b *)
let ext env x v = fun y -> if x=y then v else env y

(* eval2 : exp -> (string -> int code) -> (string -> (int -> int) code)
   -> int code *)
let rec eval2 e env fenv =
  match e with
    Int i -> .<i>.
  | Var s -> env s
  | App (s,e2) -> let rator = (fenv s) and rand = (eval2 e2 env fenv) in
    .<(.~ rator) (.~ rand)>.
  | Add (e1,e2)-> .<.~(eval2 e1 env fenv)+ .~(eval2 e2 env fenv)>.
  | Sub (e1,e2)-> .<.~(eval2 e1 env fenv)- .~(eval2 e2 env fenv)>.
  | Mul (e1,e2)-> .<.~(eval2 e1 env fenv)* .~(eval2 e2 env fenv)>.
  | Div (e1,e2)-> .<.~(eval2 e1 env fenv)/ .~(eval2 e2 env fenv)>.
  | Ifz (e1,e2,e3) -> .<if .~(eval2 e1 env fenv)=0
  then .~(eval2 e2 env fenv)
  else .~(eval2 e3 env fenv)>.

(* peval2 : prog -> (string -> int code) -> (string -> (int -> int) code)
   -> int code *)
let rec peval2 p env fenv=
  match p with
    Program ([],e) -> eval2 e env fenv
  |Program (Declaration (s1,s2,e1)::tl,e) ->
      .<let rec f x = .~(eval2 e1 (ext env s2 (.<x>.))
                           (ext fenv s1 (.<f>.)))
      in .~(peval2 (Program(tl,e)) env (ext fenv s1 (.<f>.)))>.

let cfact = peval2 fact env0 fenv0
