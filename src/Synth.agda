module Synth where

open import Core
open import Norm
open import Data.List using(List; []; _∷_; concatMap; _++_; map)
open import Data.Product using (∃-syntax; _,_)
open import Data.Maybe using(Maybe; just; nothing)

infixr 20 _<|<_

_<|<_ : ∀{A : Set} → List A → List A → List A
xs@(_ ∷ _) <|< ys = xs
[] <|< ys = ys

_>>=_ : ∀{A B : Set} → List A → (A → List B) → List B
xs >>= k = concatMap k xs

pure : ∀{A : Set} → A → List A
pure x = x ∷ []

fail : ∀{A : Set} → List A
fail = []

fetch : ∀ Γ → List (∃[ i ] ∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ = fail
fetch (∙ ◂ A) = pure (0 , A , here)
fetch (Γ ◂ A) = ((0 , A , here) ∷ map (λ (i , A , i∈Γ) → suc i , A , there i∈Γ) (fetch Γ))

synth : ℕ → ∀ Γ A → List (∃[ a ] (Γ ⊢ a ∶ A))
apply : ℕ → ∀ Γ (A a : Tm) → Γ ⊢ a ∶ A → List (∃[ b ] ∃[ B ] (Γ ⊢ b ∶ B))

synth zero _ _ = fail
synth (suc n) Γ A =
    (do
        i , _ , i∈Γ ← fetch Γ
        a , B , a∶B ← apply n Γ _ (var i) (tp-var i∈Γ)
        just (C , A≈C) ← pure (norm Γ A) where
            nothing → fail
        just (D , B≈D) ← pure (norm Γ B) where
            nothing → fail
        yes refl ← pure (eq C D) where
            no _ → fail
        pure (a , conv (≈trans B≈D (≈sym A≈C)) a∶B)) ++
    (help A)
  where
    help : ∀ A → List (∃[ a ] (Γ ⊢ a ∶ A))
    help (Π A B) = do
        b , tp-b ← synth n (shfCtx (Γ ◂ A)) B
        pure (λ' b , tp-λ tp-b)
    help _ = fail

apply zero _ _ _ _ = fail
apply (suc n) Γ G f tp-f = pure (f , G , tp-f) ++ help G f tp-f where
    help : ∀ G f → Γ ⊢ f ∶ G → List (∃[ b ] ∃[ B ] (Γ ⊢ b ∶ B))
    help (Π A B) f tp-f = do
        a , tp-a ← synth n Γ A
        b , B , tp-b ← apply n Γ (sub B a) (f $ a) (tp-$ tp-f tp-a)
        pure (b , B , tp-b)
    help _ _ _ = fail