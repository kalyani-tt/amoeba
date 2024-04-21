open Amoeba_core.Core

val commands : (string, tactic * (string list -> unit)) Hashtbl.t
val views : (string, goals -> string) Hashtbl.t
val view : string ref