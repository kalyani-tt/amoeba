open Syntax

type ctx =
| Nil
| Snoc of ctx * term

val shift_ctx : ctx -> ctx
val snoc : ctx -> term -> ctx

type goals
type tactic = goals -> goals
val init : ctx -> term -> goals
val subgoal_ctx : goals -> ctx
val subgoal_typ : goals -> term
val is_done : goals -> bool

exception CoreFail of string

val typ : tactic
val var : tactic
val lam : tactic
val app : tactic
val arr : tactic
val eql : tactic
val cst : tactic
val wkn : tactic
val axm : tactic
val nop : tactic