module Norm where

open import Core
open import Data.Maybe
open import Data.List using(List; []; _∷_)
open import Data.String using(String)
open import Data.Product

defaultFuel = 100000

norm : ∀ Γ a → Maybe (∃[ b ] (Γ ⊢ a ≈ b))
norm Γ a = help defaultFuel a where
    help : ℕ → ∀ a → Maybe (∃[ b ] (Γ ⊢ a ≈ b))
    help zero a = nothing
    help (suc n) (var i) = do
        just (j , a , p) ← just (search Γ i) where
            nothing → just (var i , ≈refl)
        c , q ← help n a
        just (c , ≈trans (ext (tp-var p)) q)
        where
            search : ∀ Γ i → Maybe (∃[ j ] ∃[ a ] (j ∶ (var i ≈ a) ∈ Γ))
            search ∙ i = nothing
            search (Γ ◂ (var j ≈ a)) i with i ≟ j
            ... | yes refl = just (0 , a , here)
            ... | no _ =
                search Γ i >>= λ (k , b , k∈Γ) →
                just (suc k , b , there k∈Γ)
            search (Γ ◂ _) i =
                search Γ i >>= λ (k , b , k∈Γ) →
                just (suc k , b , there k∈Γ)
    help (suc n) (f $ a) = do
        c , q ← help n a
        λ' b , p ← help n f where
            g , r → just ((g $ c) , $≈$ r q)
        e , r ← help n (sub b c)
        just (e , ≈trans ($≈$ p q) (≈trans λ≈β r))
    help (suc n) (λ' b) = do
        d , p ← help n b
        just (λ' d , λ≈λ p)
    help (suc n) (Π A B) = do
        C , p ← help n A
        D , q ← help n B
        just (Π C D , Π≈Π p q)
    help (suc n) U = just (U , ≈refl)
    help (suc n) (a ≈ b) = do
        c , p ← help n a
        d , q ← help n b
        just ((c ≈ d) , ≈≈≈ p q)
    help (suc n) P = just (P , ≈refl)
    help (suc n) (A ⇒ B) = do
        C , p ← help n A
        D , q ← help n B
        just ((C ⇒ D) , ⇒≈⇒ p q)