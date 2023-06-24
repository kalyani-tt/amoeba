module Elab where

open import Info
open import Core
open import Data.List using(List; []; _∷_)
open import Data.String using(String; _++_)
open import Data.Product
open import Data.Nat
open import Data.Maybe using(Maybe; just; nothing) renaming(_>>=_ to _m>>=_)

Scope = List String

record Error : Set where
    constructor error
    field
        line col : ℕ
        msg : String

data Elab (A : Set) : Set where
    ok : (a : A) → Elab A
    er : (e : Error) → Elab A

_>>=_ : ∀{A B} → Elab A → (A → Elab B) → Elab B
ok a >>= k = k a
er e >>= k = er e

elab : (γ : Sig) → SigInfo γ → Elab (∙ ⊢ γ wf)
check : ∀ Γ a A → TmInfo a → Scope → Elab (Γ ⊢ a ∶ A)
infer : ∀ Γ a → TmInfo a → Scope → Elab (∃[ A ] (Γ ⊢ a ∶ A))
convert : Scope → ℕ → ℕ → ∀ Γ a b → Elab (Γ ⊢ a ≈ b)
isΠ : Scope → ℕ → ℕ → ∀ Γ a → Elab (∃[ A ] ∃[ B ] (Γ ⊢ Π A B ≈ a))

elab γ γi = help ∙ γ γi [] where
    help : ∀ Γ γ → SigInfo γ → Scope → Elab (Γ ⊢ γ wf)
    help Γ ∙ _ _ = ok ∙-wf
    help Γ (A ◃ γ) (siginfo _ _ (Ai ◃ bn ∶ γi)) ss = do
        tp-A ← check Γ A U Ai ss
        γ-wf ← help (shfCtx (Γ ◂ A)) γ γi (bn ∷ ss)
        ok (◃-wf tp-A γ-wf)

check Γ (λ' b) G (tminfo line col (λ' bn bi)) ss = do
    A , B , Π≈G ← isΠ ss line col Γ G
    tp-b ← check (shfCtx (Γ ◂ A)) b B bi (bn ∷ ss)
    ok (conv Π≈G (tp-λ tp-b))
check Γ a A ai@(tminfo line col _) ss = do
    B , tp-a ← infer Γ a ai ss
    B≈A ← convert ss line col Γ B A
    ok (conv B≈A tp-a)

fetch : ℕ → ℕ → ∀ Γ i → Elab (∃[ A ] (i ∶ A ∈ Γ))
fetch line col ∙ i = er (error line col "No such variable")
fetch line col (Γ ◂ A) zero = ok (A , here)
fetch line col (Γ ◂ A) (suc i) = do
    A , i∈Γ ← fetch line col Γ i
    ok (A , there i∈Γ)

infer Γ (var i) (tminfo line col _) ss = do
    A , i∈Γ ← fetch line col Γ i
    ok (A , tp-var i∈Γ)
infer Γ (f $ a) (tminfo _ _ (fi@(tminfo line col _) $ ai)) ss = do
    F , tp-f ← infer Γ f fi ss
    A , B , Π≈F ← isΠ ss line col Γ F
    tp-a ← check Γ a A ai ss
    ok (sub B a , tp-$ (conv (≈sym Π≈F) tp-f) tp-a)
infer Γ (Π A B) (tminfo _ _ (Π bn Ai Bi)) ss = do
    tp-A ← check Γ A U Ai ss
    tp-B ← check (shfCtx (Γ ◂ A)) B U Bi (bn ∷ ss)
    ok (U , tp-Π tp-A tp-B)
infer Γ U _ _ = ok (U , tp-U)
infer Γ (a ≈ b) (tminfo line col (ai ≈ bi)) ss = do
    _ ← infer Γ a ai ss
    _ ← infer Γ b bi ss
    ok (U , tp-≈)
infer Γ _ (tminfo line col _) _ = er (error line col "Cannot infer type of term")

defaultFuel = 100000

norm : List String → ℕ → ℕ → ∀ Γ a → Elab (∃[ b ] (Γ ⊢ a ≈ b))
norm ns line col Γ a = help defaultFuel a where
    help : ℕ → ∀ a → Elab (∃[ b ] (Γ ⊢ a ≈ b))
    help zero a = er (error line col ("Ran out of fuel normalizing term `" ++ pretty ns a ++ "`"))
    help (suc n) (var i) = do
        just (j , a , p) ← ok (search Γ i) where
            nothing → ok (var i , ≈refl)
        c , q ← help n a
        ok (c , ≈trans (ext (tp-var p)) q)
        where
            search : ∀ Γ i → Maybe (∃[ j ] ∃[ a ] (j ∶ (var i ≈ a) ∈ Γ))
            search ∙ i = nothing
            search (Γ ◂ (var j ≈ a)) i with i ≟ j
            ... | yes refl = just (0 , a , here)
            ... | no _ =
                search Γ i m>>= λ (k , b , k∈Γ) →
                just (suc k , b , there k∈Γ)
            search (Γ ◂ _) i =
                search Γ i m>>= λ (k , b , k∈Γ) →
                just (suc k , b , there k∈Γ)
    help (suc n) (f $ a) = do
        c , q ← help n a
        λ' b , p ← help n f where
            g , r → ok ((g $ c) , $≈$ r q)
        e , r ← help n (sub b c)
        ok (e , ≈trans ($≈$ p q) (≈trans λ≈β r))
    help (suc n) (λ' b) = do
        d , p ← help n b
        ok (λ' d , λ≈λ p)
    help (suc n) (Π A B) = do
        C , p ← help n A
        D , q ← help n B
        ok (Π C D , Π≈Π p q)
    help (suc n) U = ok (U , ≈refl)
    help (suc n) (a ≈ b) = do
        c , p ← help n a
        d , q ← help n b
        ok ((c ≈ d) , ≈≈≈ p q)

convert ns line col Γ a b = do
    c , a≈c ← norm ns line col Γ a
    d , b≈d ← norm ns line col Γ b
    refl ← help (eq c d)
    ok (≈trans a≈c (≈sym b≈d))
    where
        help : Dec (c ≡ d) → Elab (c ≡ d)
        help (yes p) = ok p
        help (no _) = er (error line col ("Could not convert terms `" ++ pretty ns a ++ "` and `" ++ pretty ns b ++ "`"))

isΠ ns line col Γ a = do
    Π A B , a≈Π ← norm ns line col Γ a where
        _ → er (error line col ("Could not convert term `" ++ pretty ns a ++ "` to a pi type"))
    ok (A , B , ≈sym a≈Π)