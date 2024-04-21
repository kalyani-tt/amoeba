open Amoeba_core
open Syntax
open Core

let commands = Hashtbl.create 1

let views = Hashtbl.create 1

let view = ref "none"