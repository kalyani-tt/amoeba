module Elab where

open import Norm
open import Info
open import Core
open import Data.List using(List; []; _∷_)
open import Data.String using(String; _++_)
open import Data.Product
open import Data.Nat
open import Data.Maybe using(Maybe; just; nothing) renaming(_>>=_ to _m>>=_)
open import Data.Sum using(_⊎_; inj₁; inj₂; [_,_])

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

_>>_ : ∀{A B} → Elab A → Elab B → Elab B
a >> b = a >>= λ _ → b

_<|>_ : ∀{A} → Elab A → Elab A → Elab A
ok a <|> _ = ok a
er e <|> ok a = ok a
_ <|> er e = er e

elab : (γ : Sig) → SigInfo γ → Elab (∙ ⊢ γ wf)
check : ∀ Γ a A → TmInfo a → Scope → Elab (Γ ⊢ a ∶ A)
infer : ∀ Γ a → TmInfo a → Scope → Elab (∃[ A ] (Γ ⊢ a ∶ A))
convert : Scope → ℕ → ℕ → ∀ Γ a b → Elab (Γ ⊢ a ≈ b)
isΠ : Scope → ℕ → ℕ → ∀ Γ a → Elab (∃[ A ] ∃[ B ] (Γ ⊢ Π A B ≈ a))
isKind : Scope → ℕ → ℕ → ∀ Γ a → Elab ((Γ ⊢ a ≈ U) ⊎ (Γ ⊢ a ≈ P))

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
    ok (conv Π≈G (tp-uλ tp-b))
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
infer Γ (Π A B) (tminfo line col (Π bn Ai Bi)) ss = do
    tp-A ← check Γ A U Ai ss
    K , tp-B ← infer (shfCtx (Γ ◂ A)) B Bi (bn ∷ ss)
    K-kn ← isKind ss line col (shfCtx (Γ ◂ A)) K
    ok (U , ([ (λ K≈U → tp-UΠ tp-A (conv K≈U tp-B)) , (λ K≈P → tp-PΠ tp-A (conv K≈P tp-B)) ] K-kn))
infer Γ U _ _ = ok (U , tp-U)
infer Γ P _ _ = ok (U , tp-P)
infer Γ (A ⇒ B) (tminfo _ _ (Ai ⇒ Bi)) ss = do
    tp-A ← check Γ A P Ai ss
    tp-B ← check Γ B P Bi ss
    ok (P , tp-⇒ tp-A tp-B)
infer Γ (a ≈ b) (tminfo line col (ai ≈ bi)) ss = do
    _ ← infer Γ a ai ss
    _ ← infer Γ b bi ss
    ok (U , tp-≈)
infer Γ _ (tminfo line col _) _ = er (error line col "Cannot infer type of term")

convert ns line col Γ a b = do
    just (c , a≈c) ← ok (norm Γ a) where
        nothing → er (error line col ("Reached maximum recursion depth normalizing term `" ++ pretty ns a ++ "`"))
    just (d , b≈d) ← ok (norm Γ b) where
        nothing → er (error line col ("Reached maximum recursion depth normalizing term `" ++ pretty ns b ++ "`"))
    refl ← help (eq c d)
    ok (≈trans a≈c (≈sym b≈d))
    where
        help : Dec (c ≡ d) → Elab (c ≡ d)
        help (yes p) = ok p
        help (no _) = er (error line col ("Could not convert terms `" ++ pretty ns a ++ "` and `" ++ pretty ns b ++ "`"))

isΠ ns line col Γ a = do
    just (Π A B , a≈Π) ← ok (norm Γ a) where
        _ → er (error line col ("Could not convert term `" ++ pretty ns a ++ "` to a pi type"))
    ok (A , B , ≈sym a≈Π)

isKind ns line col Γ a =
    (do
        just (U , a≈U) ← ok (norm Γ a) where
            _ → er (error line col ("Not a U"))
        ok (inj₁ a≈U)) <|>
    (do
        just (P , a≈P) ← ok (norm Γ a) where
            _ → er (error line col ("Not a kind"))
        ok (inj₂ a≈P))