open Amoeba_core
open Syntax
open Core
open Amoeba_inter
open Toplevel
open State

let () =
    print_endline (Sys.getcwd ());
    init_top;
    print_endline (Hashtbl.find views !view (init Nil Typ));
    while true do
        inter ()
    done