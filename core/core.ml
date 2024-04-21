open Syntax

type ctx =
| Nil
| Snoc of ctx * term
[@@deriving show]

let rec shift_ctx = function
| Nil -> Nil
| Snoc (g, a) -> Snoc (shift_ctx g, shift a)

let snoc g a = shift_ctx (Snoc (g, a))

type goals =
| Exact of ctx * term * term
| Subgoal of ctx * term * (term -> goals)
[@@deriving show]

type tactic = goals -> goals

exception CoreFail of string

let init g a = Subgoal (g, a, fun x -> Exact (g, a, x))

let subgoal_ctx = function
| Subgoal (g, _, _) -> g
| _ -> raise (CoreFail "subgoal_ctx")

let subgoal_typ = function
| Subgoal (_, a, _) -> a
| _ -> raise (CoreFail "subgoal_typ")

let is_done = function
| Subgoal _ -> false
| Exact _ -> true

let typ : tactic = function
| Subgoal (_, Typ, k) -> k Typ
| _ -> raise (CoreFail "Typ")

let var : tactic = function
| Subgoal (Snoc (_, a), b, k) when a = b ->
    k (Var 0)
| _ -> raise (CoreFail "var")

let lam : tactic = function
| Subgoal (g, Arr (a, b), k) ->
    Subgoal (snoc g a, b, fun e ->
    k (Lam e))
| _ -> raise (CoreFail "lam")

let app : tactic = function
| Subgoal (g, c, k) ->
    Subgoal (g, Typ, fun a ->
    Subgoal (snoc g a, Typ, fun b ->
    Subgoal (g, Arr (a, b), fun f ->
    Subgoal (g, a, fun x ->
    if subst x b = c then
        k (App (f, x))
    else
        raise (CoreFail "app coe")))))
| _ -> raise (CoreFail "app")

let arr : tactic = function
| Subgoal (g, Typ, k) ->
    Subgoal (g, Typ, fun a ->
    Subgoal (snoc g a, Typ, fun b ->
    k (Arr (a, b))))
| _ -> raise (CoreFail "arr")

let eql : tactic = function
| Subgoal (g, Typ, k) ->
    Subgoal (g, Typ, fun a ->
    Subgoal (g, Typ, fun b ->
    Subgoal (g, a, fun x ->
    Subgoal (g, b, fun y ->
    k (Eql (a, b, x, y))))))
| _ -> raise (CoreFail "eql")

let cst : tactic = function
| Subgoal (g, b, k) ->
    Subgoal (g, Typ, fun a ->
    Subgoal (g, Eql (Typ, Typ, a, b), fun _ ->
    Subgoal (g, a, k)))
| _ -> raise (CoreFail "cst")

let wkn : tactic = function
| Subgoal (Snoc (g, _), a, k) ->
    Subgoal (g, a, k)
| _ -> raise (CoreFail "wkn")

let axm : tactic = function
| Subgoal (g, b, k) ->
    Subgoal (g, Typ, fun a ->
    Subgoal (snoc g a, shift b, fun e ->
    k (Axm (a, e))))
| _ -> raise (CoreFail "axm")

let nop g = g