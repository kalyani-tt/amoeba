open Amoeba_core
open Syntax
open Core
open State

let program : string list list ref = ref []

exception Loaded_plugin
exception No_loadpath

let load_plugin name =
    try
        let paths = [] in
        let rec loop = function
        | [] -> raise Not_found
        | path::paths ->
            print_endline ("Trying path " ^ path ^ ".");
            let full_name = path ^ Filename.dir_sep ^ Dynlink.adapt_filename (name ^ ".cmo") in
            if Sys.file_exists full_name then begin
                begin try
                    Dynlink.loadfile full_name
                with
                | Dynlink.Error (Dynlink.Module_already_loaded _) -> ()
                end;
                raise Loaded_plugin
            end else
                loop paths
        in
        loop paths
    with
    | Not_found -> print_endline ("Plugin '" ^ name ^ "' not found.")
    | Loaded_plugin -> print_endline ("Loaded plugin '" ^ name ^ "'.")

let init_top =
    Hashtbl.replace commands "load_plugin" (nop, fun [name] -> load_plugin name);
    Hashtbl.replace views "none" (fun _ -> "No viewer installed.")

let rec update st = function
| [] -> st
| (cmd::args)::cmds ->
    let (tac, upd) = Hashtbl.find commands cmd in
    let st' = tac st in
    upd args;
    update st' cmds

let inter () =
    try
        let cmd = List.filter (fun s -> s <> " ") (String.split_on_char ' ' (read_line ())) in
        program := List.append !program [cmd];
        let state = update (init Nil Typ) !program in
        print_endline (Hashtbl.find views !view state)
    with Not_found -> print_endline "No such command."