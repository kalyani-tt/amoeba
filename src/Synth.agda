module Synth where

open import Core
open import Norm
open import Data.List using(List; []; _∷_; concatMap; _++_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Maybe using(Maybe; just; nothing)

_>>=_ : ∀{A B : Set} → List A → (A → List B) → List B
xs >>= k = concatMap k xs

pure : ∀{A : Set} → A → List A
pure x = x ∷ []

fail : ∀{A : Set} → List A
fail = []

fetch : ∀ Γ → List (∃[ i ] ∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ = fail
fetch (∙ ◂ A) = pure (0 , A , here)
fetch (Γ ◂ A) = do
    i , B , i∈Γ ← fetch Γ
    ((0 , A , here) ∷ (suc i , B , there i∈Γ) ∷ [])

synth : ℕ → ∀ Γ A → List (∃[ a ] (Γ ⊢ a ∶ A))
apply : ℕ → ∀ Γ (A a : Tm) → Γ ⊢ a ∶ A → List (∃[ b ] ∃[ B ] (Γ ⊢ b ∶ B))

synth zero _ _ = fail
synth (suc n) Γ (Π A B) = do
    b , tp-b ← synth n (shfCtx (Γ ◂ A)) B
    pure (λ' b , tp-λ tp-b)
synth (suc n) Γ A = do
    i , _ , i∈Γ ← fetch Γ
    a , B , a∶B ← apply n Γ _ (var i) (tp-var i∈Γ)
    just (C , A≈C) ← pure (norm Γ A) where
        nothing → fail
    just (D , B≈D) ← pure (norm Γ B) where
        nothing → fail
    yes refl ← pure (eq C D) where
        no _ → fail
    pure (a , conv (≈trans B≈D (≈sym A≈C)) a∶B)

apply zero _ _ _ _ = fail
apply (suc n) Γ (Π A B) f tp-f = do
    a , tp-a ← synth n Γ A
    pure (f $ a , sub B a , tp-$ tp-f tp-a)
apply (suc n) Γ A a tp-a = pure (a , A , tp-a)