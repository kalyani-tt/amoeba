type term =
| Typ
| Var of int
| Lam of term
| App of term * term
| Arr of term * term
| Eql of term * term * term * term
| Axm of term * term
[@@deriving show]

let rec prec0 ns = function
| Typ -> "U"
| Var i -> List.nth ns i
| e -> "(" ^ prec2 ns e ^ ")"
and prec1 ns = function
| App (f, x) -> prec1 ns f ^ " " ^ prec0 ns x
| e -> prec0 ns e
and prec2 ns = function
| Lam e -> "λ_. " ^ prec2 ("_"::ns) e
| Arr (a, b) -> "(_ : " ^ prec2 ns a ^ ") -> " ^ prec2 ("_"::ns) b
| Eql (_, _, x, y) -> prec1 ns x ^ " = " ^ prec1 ns y
| Axm _ -> failwith "Can't pretty print axiom"
| e -> prec1 ns e

let pretty = prec2

let rec shift_aux n = function
| Typ -> Typ
| Var i ->
    if i < n then
        Var i
    else
        Var (1 + i)
| Lam e -> Lam (shift_aux (1 + n) e)
| App (f, x) -> App (shift_aux n f, shift_aux n x)
| Arr (a, b) -> Arr (shift_aux n a, shift_aux n b)
| Eql (a, b, x, y) -> Eql (shift_aux n a, shift_aux n b, shift_aux n x, shift_aux n y)
| Axm (a, e) -> Axm (shift_aux n a, shift_aux n e)

let shift = shift_aux 0

let rec subst_aux n r = function
| Typ -> Typ
| Var i ->
    if i = n then
        r
    else if i < n then
        Var i
    else
        Var (i - 1)
| Lam e -> Lam (subst_aux (1 + n) (shift r) e)
| App (f, x) -> App (subst_aux n r f, subst_aux n r x)
| Arr (a, b) -> Arr (subst_aux n r a, subst_aux n r b)
| Eql (a, b, x, y) -> Eql (subst_aux n r a, subst_aux n r b, subst_aux n r x, subst_aux n r y)
| Axm (a, e) -> Axm (subst_aux n r a, subst_aux (1 + n) (shift r) e)

let subst = subst_aux 0