module Tactic where

infixr 20 _&_

open import Core
open import Data.Sum as Sum
import Data.Maybe as Maybe
open import Data.Maybe using(Maybe; just; nothing)
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function using(id; case_of_; _∘_)
open import Data.List hiding(_++_) public
open import Data.String using(String; _++_) renaming(_≟_ to eqStr)

Name = String
Error = String

pattern ok a = inj₂ a
pattern er e = inj₁ e

_>>=_ : {A B C : Set} → A ⊎ B → (B → A ⊎ C) → A ⊎ C
er e >>= k = er e
ok a >>= k = k a

record Context : Set where
    constructor context
    field
        bindings : List Name
open Context public

addName : Name → Context → Context
addName v s = record s { bindings = v ∷ bindings s }

data Mode : Set where
    mcheck minfer msynth : Mode

modeInp : Mode → Set
modeInp mcheck = Ty
modeInp minfer = ⊤
modeInp msynth = ⊤

modeOut : ∀ m → Ctx → modeInp m → Set
modeOut mcheck Δ B = ∃[ b ] (Δ ⊢ b ∶ B)
modeOut minfer Δ tt = ∃[ b ] ∃[ B ] ((Δ ⊢ b ∶ B))
modeOut msynth Δ tt = ∃[ b ] (len Δ ⊢ b tm)

data Holes (Γ : Ctx) (A : Ty) : Set where
    done : String → ∀ a → (tp-a : Γ ⊢ a ∶ A) → Holes Γ A
    subgoal : Context → ∀ m Δ inp → (k : String → modeOut m Δ inp → Holes Γ A) → Holes Γ A

pattern check s Γ A k = subgoal s mcheck Γ A k
pattern infer s Γ k = subgoal s minfer Γ tt k
pattern synth s Γ k = subgoal s msynth Γ tt k

Tactic : Set
Tactic = ∀{Γ A} → Holes Γ A → Error ⊎ Holes Γ A

fillOut : ∀ m Γ inp → modeOut m Γ inp
fillOut mcheck Γ inp = hole , tp-hole
fillOut minfer Γ inp = hole , hole , tp-hole
fillOut msynth Γ inp = hole , hole-tm

fill : Holes Γ A → String × ∃[ a ] (Γ ⊢ a ∶ A)
fill (done x a tp-a) = x , a , tp-a
fill (subgoal x m Δ inp k) = fill (k "[?]" (fillOut m Δ inp))

run : ∀ Γ A → Tactic → Error ⊎ Holes Γ A
run Γ A t = t (check (context []) Γ A λ doc (b , tp-b) → done doc b tp-b)

runFill : ∀ Γ A → Tactic → Error ⊎ (String × ∃[ a ] (Γ ⊢ a ∶ A))
runFill Γ A t = Sum.map id fill (run Γ A t)

fetch : ∀ Γ i → Maybe (∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ i = nothing
fetch (Γ ◂ A) zero = just (A , here)
fetch (Γ ◂ B) (suc i) = Maybe.map (λ (A , i∈Γ) → A , there i∈Γ) (fetch Γ i)

getIndex : Name → List Name → Error ⊎ ℕ
getIndex v [] = er "getIndex"
getIndex v (x ∷ vs) with eqStr v x
... | yes refl = ok 0
... | no _ = Sum.map id suc (getIndex v vs)

getVar : ∀ Γ → Name → List Name → Error ⊎ ∃[ i ] ∃[ A ] (i ∶ A ∈ Γ)
getVar Γ v vs = do
    i ← getIndex v vs
    just (A , i∈Γ) ← ok (fetch Γ i) where
        nothing → er ("No var '" ++ v ++ "'")
    ok (i , A , i∈Γ)

_&_ : Tactic → Tactic → Tactic
(f & g) h with f h
... | ok h' = g h'
... | er e = er e

ascribe : Tactic
ascribe (infer s Γ k) = ok
    (check s Γ U λ Ad (A , tp-A) →
     check s Γ A λ ad (a , tp-a) →
     k (ad ++ " : " ++ Ad) (a , A , tp-a))
ascribe _ = er "ascribe"

parens : Tactic
parens (subgoal s m Γ inp k) = ok
    (subgoal s m Γ inp λ doc out →
     k ("(" ++ doc ++ ")") out)
parens _ = er "parens"

intros : List Name → Tactic
intros [] s = ok s
intros vs = help (λ bd → "λ" ++ names vs ++ ". " ++ bd) vs where
    names : List Name → String
    names [] = ""
    names (v ∷ []) = v
    names (v ∷ vs) = v ++ " " ++ names vs

    help : (String → String) → List Name → Tactic
    help f (v ∷ vs) (check s Γ (Π A B) k) = help f vs
        (check (addName v s) (shfCtx (Γ ◂ A)) B λ bd (b , tp-b) → k bd (λ' b , tp-λ tp-b))
    help f [] (check s Γ B k) = ok (check s Γ B λ bd out → k (f bd) out)
    help _ _ _ = er "intros"

apply : Name → Tactic
apply v {ctx} {goal} (infer s Γ k) = do
    i , A , i∈Γ ← getVar Γ v (bindings s)
    ok (help 1000 v A (tp-var i∈Γ))
  where
    help : ℕ → String → ∀ A → Γ ⊢ f ∶ A → Holes ctx goal
    help zero acc A tp-a = k acc (_ , A , tp-a)
    help (suc n) acc (Π A B) tp-f =
        check s Γ A λ ad (a , tp-a) →
        help n (acc ++ " " ++ ad) (sub B a) (tp-$ tp-f tp-a)
    help (suc n) acc A tp-a = k acc (_ , A , tp-a)
apply _ _ = er "apply"

Pi : Name → Tactic
Pi v (infer s Γ k) = ok
    (check s Γ U λ Ad (A , tp-A) →
     check (record s { bindings = v ∷ bindings s }) (shfCtx (Γ ◂ A)) U λ Bd (B , tp-B) →
     k ("Π" ++ v ++ " : " ++ Ad ++ ". " ++ Bd) (Π A B , U , tp-Π tp-A tp-B))
Pi _ _ = er "Pi"

Univ : Tactic
Univ (infer s Γ k) = ok (k "Type" (U , U , tp-U))
Univ _ = er "Univ"

Eq : Tactic
Eq (infer s Γ k) = ok
    (synth s Γ λ ad (a , a-tm) →
     synth s Γ λ bd (b , b-tm) →
     k (ad ++ " = " ++ bd) ((a ≈ b) , U , tp-≈ a-tm b-tm))
Eq _ = er "Eq"

hyp : Name → Tactic
hyp v (infer s Γ k) = do
    i , A , i∈Γ ← getVar Γ v (bindings s)
    ok (k v (var i ,  A , tp-var i∈Γ))
hyp _ _ = er "hyp"

convert : Tactic
convert (check s Γ A k) = ok
    (infer s Γ λ bd (b , B , tp-b) →
     check s Γ (B ≈ A) λ _ (p , tp-p) →
     k bd (b , conv (ext tp-p) tp-b))
convert _ = er "convert"

erasure : Tactic
erasure (synth s Γ k) = ok
    (infer s Γ λ ad (a , A , tp-a) →
     k ad (a , erase tp-a))
erasure _ = er "erasure"

eqRefl : Tactic
eqRefl (infer s Γ k) = ok
    (synth s Γ λ _ (a , a-tm) →
     k "refl" (rfl , (a ≈ a) , tp-rfl ≈refl))
eqRefl _ = er "eqRefl"

eqSym : Tactic
eqSym (check s Γ (a ≈ b) k) = ok
    (check s Γ (b ≈ a) λ pd (p , tp-p) →
     k ("sym " ++ pd) (rfl , tp-rfl (ext tp-hole)) )
eqSym _ = er "eqSym"

eqTrans : Tactic
eqTrans (check s Γ (a ≈ c) k) = ok
    (synth s Γ λ _ (b , b-tm) →
     check s Γ (a ≈ b) λ pd (p , tp-p) →
     check s Γ (b ≈ c) λ qd (q , tp-q) →
     k (pd ++ " ∙ " ++ qd) (rfl , tp-rfl (≈trans (ext tp-p) (ext tp-q))))
eqTrans _ = er "eqTrans"

eqApps : Tactic
eqApps (check s Γ (f $ a ≈ g $ b) k) = ok
    (check s Γ (f ≈ g) λ pd (p , tp-p) →
     check s Γ (a ≈ b) λ qd (q , tp-q) →
     k ("cong-$ " ++ pd ++ " " ++ qd) (rfl , tp-rfl ($≈$ (ext tp-p) (ext tp-q))))
eqApps _ = er "eqApps"

eqLams : Tactic
eqLams (check s Γ (λ' b ≈ λ' d) k) = ok
    (check s Γ (b ≈ d) λ pd (p , tp-p) →
     k ("funext " ++ pd) (rfl , tp-rfl (λ≈λ (ext tp-p))))
eqLams _ = er "eqLams"

eqBeta : Tactic
eqBeta (infer s Γ k) = ok
    (synth s Γ λ _ (b , b-tm) →
     synth s Γ λ _ (a , a-tm) →
     k "β" (rfl , (λ' b $ a ≈ sub b a) , tp-rfl λ≈β))
eqBeta _ = er "eqBeta"

eqPis : Tactic
eqPis (check s Γ (Π A B ≈ Π C D) k) = ok
    (check s Γ (A ≈ C) λ pd (p , tp-p) →
     check s Γ (B ≈ D) λ qd (q , tp-q) →
     k ("cong-Π " ++ pd ++ " " ++ qd) (rfl , tp-rfl (Π≈Π (ext tp-p) (ext tp-q))))
eqPis _ = er "eqPis"

eqEqs : Tactic
eqEqs (check s Γ ((a ≈ b) ≈ (c ≈ d)) k) = ok
    (check s Γ (a ≈ c) λ pd (p , tp-p) →
     check s Γ (b ≈ d) λ qd (q , tp-q) →
     k ("cong-= " ++ pd ++ " " ++ qd) (rfl , tp-rfl (≈≈≈ (ext tp-p) (ext tp-q))))
eqEqs _ = er "eqEqs"