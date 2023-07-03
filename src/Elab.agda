open import Core

module Elab (ctx : Ctx) (goal : Ty) where

infixr 20 _&_

open import Data.Sum as Sum
open import Data.Nat
open import Data.Product
open import Function using(id; case_of_; _∘_)
open import Data.List public
open import Data.String using(String) renaming(_≟_ to eqStr)

Name = String

data Error : Set where
    ??? : Error

pattern ok a = inj₂ a
pattern er e = inj₁ e

_>>=_ : {A B C : Set} → A ⊎ B → (B → A ⊎ C) → A ⊎ C
er e >>= k = er e
ok a >>= k = k a

data Mode : Set where
    check infer synth : Mode

Modes = List Mode

variable
    ms ns rs : Modes
    n m : Mode

record State : Set where
    constructor state
    field
        bindings : List Name
open State public

data Holes (Γ : Ctx) (A : Ty) : Modes → Set where
    done : ∀ a → (tp-a : Γ ⊢ a ∶ A) → Holes Γ A []
    check : State → ∀ Δ B → (k : ∀ b → Δ ⊢ b ∶ B → Error ⊎ Holes Γ A ms) → Holes Γ A (check ∷ ms)
    infer : State → ∀ Δ → (k : ∀ b B → Δ ⊢ b ∶ B → Error ⊎ Holes Γ A ms) → Holes Γ A (infer ∷ ms)
    synth : State → ∀ Δ → (k : ∀ b → len Δ ⊢ b tm → Error ⊎ Holes Γ A ms) → Holes Γ A (synth ∷ ms)
error : {A : Set} → Error ⊎ A
error = inj₁ ???

Tactic : Modes → Modes → Set
Tactic ms ns = ∀{Γ A} → Holes Γ A ms → Error ⊎ Holes Γ A ns

run : Tactic (check ∷ []) [] → Error ⊎ (∃[ a ] (ctx ⊢ a ∶ goal))
run t with t (check (state []) ctx goal (λ b z → ok (done b z)))
... | ok (done a tp-a) = inj₂ (a , tp-a)
... | er e = er e

_&_ : Tactic ns ms → Tactic ms rs → Tactic ns rs
(f & g) h with f h
... | ok h' = g h'
... | er e = er e

switch : Tactic (check ∷ ms) (infer ∷ ms)
switch (check s Γ A k) = ok
    (infer s Γ λ a B tp-a →
     case eq A B of λ
     { (yes refl) → k a tp-a
     ; (no _) → error })

ascribe : Tactic (infer ∷ ms) (check ∷ check ∷ ms)
ascribe (infer s Γ k) = ok
    (check s Γ U λ A tp-A → ok
    (check s Γ A λ a tp-a →
     k a A tp-a))

intro : Name → Tactic (check ∷ ms) (check ∷ ms)
intro v (check s Γ (Π A B) k) = ok
    (check (record s { bindings = v ∷ bindings s }) (shfCtx (Γ ◂ A)) B λ b tp-b →
     k (λ' b) (tp-λ tp-b))
intro v (check s Γ A k) = error

apply : Tactic (infer ∷ ms) (infer ∷ check ∷ ms)
apply (infer s Γ k) = ok
    (infer s Γ λ
     { f (Π A B) tp-f → ok
       (check s Γ A λ a tp-a →
        k (f $ a) (sub B a) (tp-$ tp-f tp-a))
     ; _ _ _ → error })

Pi : Name → Tactic (infer ∷ ms) (check ∷ check ∷ ms)
Pi v (infer s Γ k) = ok
    (check s Γ U λ A tp-A → ok
    (check (record s { bindings = v ∷ bindings s }) (shfCtx (Γ ◂ A)) U λ B tp-B →
     k (Π A B) U (tp-Π tp-A tp-B)))

Univ : Tactic (infer ∷ ms) ms
Univ (infer s Γ k) = k U U tp-U

Eq : Tactic (infer ∷ ms) (synth ∷ synth ∷ ms)
Eq (infer s Γ k) = ok
    (synth s Γ λ a a-tm → ok
    (synth s Γ λ b b-tm →
     k (a ≈ b) U (tp-≈ a-tm b-tm)))

fetch : ∀ Γ i → Error ⊎ (∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ i = error
fetch (Γ ◂ A) zero = ok (A , here)
fetch (Γ ◂ B) (suc i) = Sum.map id (λ (A , i∈Γ) → A , there i∈Γ) (fetch Γ i)

getIndex : Name → List Name → Error ⊎ ℕ
getIndex v [] = error
getIndex v (x ∷ vs) with eqStr v x
... | yes refl = ok 0
... | no _ = Sum.map id suc (getIndex v vs)

hyp : Name → Tactic (infer ∷ ms) ms
hyp v (infer s Γ k) = do
    i ← getIndex v (bindings s)
    A , i∈Γ ← fetch Γ i
    k (var i) A (tp-var i∈Γ)

convert : Tactic (check ∷ ms) (infer ∷ check ∷ ms)
convert (check s Γ A k) = ok
    (infer s Γ λ b B tp-b → ok
    (check s Γ (B ≈ A) λ p tp-p →
     k b (conv (ext tp-p) tp-b)))

erasure : Tactic (synth ∷ ms) (infer ∷ ms)
erasure (synth s Γ k) = ok
    (infer s Γ λ a A tp-a →
     k a (erase tp-a))

eqRefl : Tactic (infer ∷ ms) (synth ∷ ms)
eqRefl (infer s Γ k) = ok
    (synth s Γ λ a a-tm →
     k rfl (a ≈ a) (tp-rfl ≈refl))

eqSym : Tactic (infer ∷ ms) (infer ∷ ms)
eqSym (infer s Γ k) = ok
    (infer s Γ λ
     { p (a ≈ b) tp-p → k rfl (b ≈ a) (tp-rfl (≈sym (ext tp-p)))
     ; _ _ _ → error})

eqTrans : Tactic (check ∷ ms) (synth ∷ check ∷ check ∷ ms)
eqTrans (check s Γ (a ≈ c) k) = ok
    (synth s Γ λ b b-tm → ok
    (check s Γ (a ≈ b) λ p tp-p → ok
    (check s Γ (b ≈ c) λ q tp-q →
     k rfl (tp-rfl (≈trans (ext tp-p) (ext tp-q))))))
eqTrans _ = error

eqApps : Tactic (check ∷ ms) (check ∷ check ∷ ms)
eqApps (check s Γ (f $ a ≈ g $ b) k) = ok
    (check s Γ (f ≈ g) λ p tp-p → ok
    (check s Γ (a ≈ b) λ q tp-q →
     k rfl (tp-rfl ($≈$ (ext tp-p) (ext tp-q)))))
eqApps _ = error

eqLams : Tactic (check ∷ ms) (check ∷ ms)
eqLams (check s Γ (λ' b ≈ λ' d) k) = ok
    (check s Γ (b ≈ d) λ p tp-p →
     k rfl (tp-rfl (λ≈λ (ext tp-p))))
eqLams _ = error

eqBeta : Tactic (infer ∷ ms) (synth ∷ synth ∷ ms)
eqBeta (infer s Γ k) = ok
    (synth s Γ λ b b-tm → ok
    (synth s Γ λ a a-tm →
     k rfl (λ' b $ a ≈ sub b a) (tp-rfl λ≈β)))

eqPis : Tactic (check ∷ ms) (check ∷ check ∷ ms)
eqPis (check s Γ (Π A B ≈ Π C D) k) = ok
    (check s Γ (A ≈ C) λ p tp-p → ok
    (check s Γ (B ≈ D) λ q tp-q →
     k rfl (tp-rfl (Π≈Π (ext tp-p) (ext tp-q)))))
eqPis _ = error

eqEqs : Tactic (check ∷ ms) (check ∷ check ∷ ms)
eqEqs (check s Γ ((a ≈ b) ≈ (c ≈ d)) k) = ok
    (check s Γ (a ≈ c) λ p tp-p → ok
    (check s Γ (b ≈ d) λ q tp-q →
     k rfl (tp-rfl (≈≈≈ (ext tp-p) (ext tp-q)))))
eqEqs _ = error