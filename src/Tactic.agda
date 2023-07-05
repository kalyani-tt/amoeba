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
    subgoal : Context → ∀ m Δ inp → (k : String → modeOut m Δ inp → Error ⊎ Holes Γ A) → Holes Γ A

pattern check s Γ A k = subgoal s mcheck Γ A k
pattern infer s Γ k = subgoal s minfer Γ tt k
pattern synth s Γ k = subgoal s msynth Γ tt k

Tactic : Set
Tactic = ∀{Γ A} → Holes Γ A → Error ⊎ Holes Γ A

run : ∀ Γ A → Tactic → Error ⊎ (String × ∃[ a ] (Γ ⊢ a ∶ A))
run Γ A t with t (check (context []) Γ A λ doc (b , tp-b) → ok (done doc b tp-b))
... | ok (done doc a tp-a) = inj₂ (doc , a , tp-a)
... | ok _ = er "Unsolved obligations"
... | er e = er e

_&_ : Tactic → Tactic → Tactic
(f & g) h with f h
... | ok h' = g h'
... | er e = er e

switch : Tactic
switch (check s Γ A k) = ok
    (infer s Γ λ doc (a , B , tp-a) →
     case eq A B of λ
     { (yes refl) → k doc (a , tp-a)
     ; (no _) → er "Types unequal"})
switch _ = er "switch"

ascribe : Tactic
ascribe (infer s Γ k) = ok
    (check s Γ U λ Ad (A , tp-A) → ok
    (check s Γ A λ ad (a , tp-a) →
     k (ad ++ " : " ++ Ad) (a , A , tp-a)))
ascribe _ = er "ascribe"

parens : Tactic
parens (subgoal s m Γ inp k) = ok
    (subgoal s m Γ inp λ doc out →
     k ("(" ++ doc ++ ")") out)
parens _ = er "parens"

intro : Name → Tactic
intro v (check s Γ (Π A B) k) = ok
    (check (record s { bindings = v ∷ bindings s }) (shfCtx (Γ ◂ A)) B λ bd (b , tp-b) →
     k ("λ" ++ v ++ ". " ++ bd) (λ' b , tp-λ tp-b))
intro _ _ = er "intro"

apply : Tactic
apply (infer s Γ k) = ok
    (infer s Γ λ
     { fd (f , Π A B , tp-f) → ok
       (check s Γ A λ ad (a , tp-a) →
        k (fd ++ " " ++ ad) (f $ a , sub B a , tp-$ tp-f tp-a))
     ; _ _ → er "Not a function type" })
apply _ = er "apply"

Pi : Name → Tactic
Pi v (infer s Γ k) = ok
    (check s Γ U λ Ad (A , tp-A) → ok
    (check (record s { bindings = v ∷ bindings s }) (shfCtx (Γ ◂ A)) U λ Bd (B , tp-B) →
     k ("Π" ++ v ++ " : " ++ Ad ++ ". " ++ Bd) (Π A B , U , tp-Π tp-A tp-B)))
Pi _ _ = er "Pi"

Univ : Tactic
Univ (infer s Γ k) = k "Type" (U , U , tp-U)
Univ _ = er "Univ"

Eq : Tactic
Eq (infer s Γ k) = ok
    (synth s Γ λ ad (a , a-tm) → ok
    (synth s Γ λ bd (b , b-tm) →
     k (ad ++ " = " ++ bd) ((a ≈ b) , U , tp-≈ a-tm b-tm)))
Eq _ = er "Eq"

fetch : ∀ Γ i → Maybe (∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ i = nothing
fetch (Γ ◂ A) zero = just (A , here)
fetch (Γ ◂ B) (suc i) = Maybe.map (λ (A , i∈Γ) → A , there i∈Γ) (fetch Γ i)

getIndex : Name → List Name → Error ⊎ ℕ
getIndex v [] = er "getIndex"
getIndex v (x ∷ vs) with eqStr v x
... | yes refl = ok 0
... | no _ = Sum.map id suc (getIndex v vs)

hyp : Name → Tactic
hyp v (infer s Γ k) = do
    i ← getIndex v (bindings s)
    just (A , i∈Γ) ← ok (fetch Γ i) where
        nothing → er ("No variable '" ++ v ++ "'")
    k v (var i ,  A , tp-var i∈Γ)
hyp _ _ = er "hyp"

convert : Tactic
convert (check s Γ A k) = ok
    (infer s Γ λ bd (b , B , tp-b) → ok
    (check s Γ (B ≈ A) λ _ (p , tp-p) →
     k bd (b , conv (ext tp-p) tp-b)))
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
eqSym (infer s Γ k) = ok
    (infer s Γ λ
     { pd (p , (a ≈ b) , tp-p) → k ("sym " ++ pd) (rfl , (b ≈ a) , tp-rfl (≈sym (ext tp-p)))
     ; _ _ → er "Not an equality type"})
eqSym _ = er "eqSym"

eqTrans : Tactic
eqTrans (check s Γ (a ≈ c) k) = ok
    (synth s Γ λ _ (b , b-tm) → ok
    (check s Γ (a ≈ b) λ pd (p , tp-p) → ok
    (check s Γ (b ≈ c) λ qd (q , tp-q) →
     k (pd ++ " ∙ " ++ qd) (rfl , tp-rfl (≈trans (ext tp-p) (ext tp-q))))))
eqTrans _ = er "eqTrans"

eqApps : Tactic
eqApps (check s Γ (f $ a ≈ g $ b) k) = ok
    (check s Γ (f ≈ g) λ pd (p , tp-p) → ok
    (check s Γ (a ≈ b) λ qd (q , tp-q) →
     k ("cong-$ " ++ pd ++ " " ++ qd) (rfl , tp-rfl ($≈$ (ext tp-p) (ext tp-q)))))
eqApps _ = er "eqApps"

eqLams : Tactic
eqLams (check s Γ (λ' b ≈ λ' d) k) = ok
    (check s Γ (b ≈ d) λ pd (p , tp-p) →
     k ("funext " ++ pd) (rfl , tp-rfl (λ≈λ (ext tp-p))))
eqLams _ = er "eqLams"

eqBeta : Tactic
eqBeta (infer s Γ k) = ok
    (synth s Γ λ _ (b , b-tm) → ok
    (synth s Γ λ _ (a , a-tm) →
     k "β" (rfl , (λ' b $ a ≈ sub b a) , tp-rfl λ≈β)))
eqBeta _ = er "eqBeta"

eqPis : Tactic
eqPis (check s Γ (Π A B ≈ Π C D) k) = ok
    (check s Γ (A ≈ C) λ pd (p , tp-p) → ok
    (check s Γ (B ≈ D) λ qd (q , tp-q) →
     k ("cong-Π " ++ pd ++ " " ++ qd) (rfl , tp-rfl (Π≈Π (ext tp-p) (ext tp-q)))))
eqPis _ = er "eqPis"

eqEqs : Tactic
eqEqs (check s Γ ((a ≈ b) ≈ (c ≈ d)) k) = ok
    (check s Γ (a ≈ c) λ pd (p , tp-p) → ok
    (check s Γ (b ≈ d) λ qd (q , tp-q) →
     k ("cong-= " ++ pd ++ " " ++ qd) (rfl , tp-rfl (≈≈≈ (ext tp-p) (ext tp-q)))))
eqEqs _ = er "eqEqs"