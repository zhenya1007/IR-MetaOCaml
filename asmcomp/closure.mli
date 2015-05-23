(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Introduction of closures, uncurrying, recognition of direct calls *)

val intro: int -> Lambda.lambda -> Clambda.ulambda
val reset : unit -> unit

(* The "I am not really a runnable closure; I just hold a bunch of values" marker *)
val ulambda_values_env_body : Clambda.ulambda

val code_description_of_ucode : Clambda.ulambda -> Lambda.code_description
