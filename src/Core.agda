module Core where

open import Data.Nat public
open import Data.Bool using(if_then_else_)
open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality using(_≡_; refl) public

infix 0 _⊢_≈_
infix 0 _∶_∈_
infix 0 _⊢_∶_
infix 0 _⊢_wf
infixl 5 _$_
infix 3 _⇒_
infix 4 _≈_
infixl 1 _◂_
infixl 1 _◃_

data Tm : Set
Ty = Tm
data Ctx : Set
data _∶_∈_ : ℕ → Ty → Ctx → Set
data _⊢_∶_ : Ctx → Tm → Ty → Set
data _⊢_≈_ : Ctx → Tm → Tm → Set
data Sig : Set          
data _⊢_wf : Ctx → Sig → Set

variable
    a b c d e f g A B C D n m p q r : Tm
    Γ Δ : Ctx
    γ δ : Sig
    i j : ℕ

data Tm where
    var : (i : ℕ) → Tm
    _$_ : (f a : Tm) → Tm
    λ' : (b : Tm) → Tm
    Π : (A B : Tm) → Tm
    _⇒_ : (A B : Tm) → Tm
    U P : Tm
    _≈_ : (a b : Tm) → Tm

shf : Tm → Tm
shf = help 0 module shf where
    help : ℕ → Tm → Tm
    help n (var i) =
        if i <ᵇ n then
            var i
        else
            var (suc i)
    help n (f $ a) = help n f $ help n a
    help n (λ' b) = λ' (help (suc n) b)
    help n (Π A B) = Π (help n A) (help (suc n) B)
    help n U = U
    help n (a ≈ b) = help n a ≈ help n b
    help n (A ⇒ B) = help n A ⇒ help n B
    help n P = P

sub : Tm → Tm → Tm
sub = help 0 where
    help : ℕ → Tm → Tm → Tm
    help n (var i) e =
        if i ≡ᵇ n then
            e
        else if i <ᵇ n then
            var i
        else
            var (pred i)
    help n (f $ a) e = help n f e $ help n a e
    help n (λ' b) e = λ' (help (suc n) b (shf.help n e))
    help n (Π A B) e = Π (help n A e) (help (suc n) B (shf.help n e))
    help n U e = U
    help n (a ≈ b) e = help n a e ≈ help n b e
    help n (A ⇒ B) e = help n A e ⇒ help n B e
    help n P e = P

data Ctx where
    ∙ : Ctx
    _◂_ : (Γ : Ctx) (A : Ty) → Ctx

shfCtx : Ctx → Ctx
shfCtx ∙ = ∙
shfCtx (Γ ◂ A) = shfCtx Γ ◂ shf A

data _∶_∈_ where
    here : 0 ∶ A ∈ Γ ◂ A
    there : i ∶ A ∈ Γ →
            suc i ∶ A ∈ Γ ◂ B

data _⊢_∶_ where
    tp-var : i ∶ A ∈ Γ →
             Γ ⊢ var i ∶ A
    tp-$ : Γ ⊢ f ∶ Π A B →
           Γ ⊢ a ∶ A →
           Γ ⊢ f $ a ∶ sub B a
    tp-uλ : shfCtx (Γ ◂ A) ⊢ b ∶ B →
            Γ ⊢ λ' b ∶ Π A B
    tp-pλ : shfCtx (Γ ◂ A) ⊢ b ∶ shf B →
            Γ ⊢ λ' b ∶ A ⇒ B
    tp-UΠ : Γ ⊢ A ∶ U →
            shfCtx (Γ ◂ A) ⊢ B ∶ U →
            Γ ⊢ Π A B ∶ U
    tp-PΠ : Γ ⊢ A ∶ U →
            shfCtx (Γ ◂ A) ⊢ B ∶ P →
            Γ ⊢ Π A B ∶ U
    tp-⇒ : Γ ⊢ A ∶ P →
            Γ ⊢ B ∶ P →
            Γ ⊢ A ⇒ B ∶ P
    tp-U : Γ ⊢ U ∶ U
    tp-P : Γ ⊢ P ∶ U
    tp-≈ : Γ ⊢ a ≈ b ∶ U
    conv : Γ ⊢ A ≈ B →
           Γ ⊢ a ∶ A →
           Γ ⊢ a ∶ B

data _⊢_≈_ where
    ≈refl : Γ ⊢ a ≈ a
    ≈sym : Γ ⊢ a ≈ b →
           Γ ⊢ b ≈ a
    ≈trans : Γ ⊢ a ≈ b →
             Γ ⊢ b ≈ c →
             Γ ⊢ a ≈ c
    $≈$ : Γ ⊢ f ≈ g →
          Γ ⊢ a ≈ b →
          Γ ⊢ f $ a ≈ g $ b
    λ≈λ : Γ ⊢ b ≈ d →
          Γ ⊢ λ' b ≈ λ' d
    λ≈β : Γ ⊢ λ' b $ a ≈ sub b a
    Π≈Π : Γ ⊢ A ≈ C →
          Γ ⊢ B ≈ D →
          Γ ⊢ Π A B ≈ Π C D
    ≈≈≈ : Γ ⊢ a ≈ c →
          Γ ⊢ b ≈ d →
          Γ ⊢ a ≈ b ≈ c ≈ d
    ⇒≈⇒ : Γ ⊢ A ≈ C →
           Γ ⊢ B ≈ D →
           Γ ⊢ A ⇒ B ≈ C ⇒ D
    ext : Γ ⊢ p ∶ a ≈ b →
          Γ ⊢ a ≈ b

data Sig where
    ∙ : Sig
    _◃_ : (A : Ty) (γ : Sig) → Sig

data _⊢_wf where
    ∙-wf : Γ ⊢ ∙ wf
    ◃-wf : Γ ⊢ A ∶ U →
            shfCtx (Γ ◂ A) ⊢ γ wf →
            Γ ⊢ A ◃ γ wf

eq : (a b : Tm) → Dec (a ≡ b)
eq (var i) (var i₁) with i ≟ i₁
... | yes refl = yes refl
... | no p = no λ { refl → p refl }
eq (var i) (b $ b₁) = no (λ ())
eq (var i) (λ' b) = no (λ ())
eq (var i) (Π b b₁) = no (λ ())
eq (var i) U = no (λ ())
eq (var i) (b ≈ b₁) = no (λ ())
eq (a $ a₁) (var i) = no (λ ())
eq (a $ b) (c $ d) with eq a c | eq b d
... | yes refl | yes refl = yes refl
... | no p     | _ = no λ { refl → p refl }
... | _        | no p = no λ { refl → p refl }
eq (a $ a₁) (λ' b) = no (λ ())
eq (a $ a₁) (Π b b₁) = no (λ ())
eq (a $ a₁) U = no (λ ())
eq (a $ a₁) (b ≈ b₁) = no (λ ())
eq (λ' a) (var i) = no (λ ())
eq (λ' a) (b $ b₁) = no (λ ())
eq (λ' a) (λ' b) with eq a b
... | yes refl = yes refl
... | no p = no λ { refl → p refl }
eq (λ' a) (Π b b₁) = no (λ ())
eq (λ' a) U = no (λ ())
eq (λ' a) (b ≈ b₁) = no (λ ())
eq (Π a a₁) (var i) = no (λ ())
eq (Π a a₁) (b $ b₁) = no (λ ())
eq (Π a a₁) (λ' b) = no (λ ())
eq (Π a b) (Π c d) with eq a c | eq b d
... | yes refl | yes refl = yes refl
... | no p     | _ = no λ { refl → p refl }
... | _        | no p = no λ { refl → p refl }
eq (Π a a₁) U = no (λ ())
eq (Π a a₁) (b ≈ b₁) = no (λ ())
eq U (var i) = no (λ ())
eq U (b $ b₁) = no (λ ())
eq U (λ' b) = no (λ ())
eq U (Π b b₁) = no (λ ())
eq U U = yes refl
eq U (b ≈ b₁) = no (λ ())
eq (a ≈ a₁) (var i) = no (λ ())
eq (a ≈ a₁) (b $ b₁) = no (λ ())
eq (a ≈ a₁) (λ' b) = no (λ ())
eq (a ≈ a₁) (Π b b₁) = no (λ ())
eq (a ≈ a₁) U = no (λ ())
eq (a ≈ b) (c ≈ d) with eq a c | eq b d
... | yes refl | yes refl = yes refl
... | no p     | _ = no λ { refl → p refl }
... | _        | no p = no λ { refl → p refl }
eq (var i) (b ⇒ b₁) = no (λ ())
eq (var i) P = no (λ ())
eq (a $ a₁) (b ⇒ b₁) = no (λ ())
eq (a $ a₁) P = no (λ ())
eq (λ' a) (b ⇒ b₁) = no (λ ())
eq (λ' a) P = no (λ ())
eq (Π a a₁) (b ⇒ b₁) = no (λ ())
eq (Π a a₁) P = no (λ ())
eq (a ⇒ a₁) (var i) = no (λ ())
eq (a ⇒ a₁) (b $ b₁) = no (λ ())
eq (a ⇒ a₁) (λ' b) = no (λ ())
eq (a ⇒ a₁) (Π b b₁) = no (λ ())
eq (a ⇒ b) (c ⇒ d) with eq a c | eq b d
... | yes refl | yes refl = yes refl
... | no p     | _ = no λ { refl → p refl }
... | _        | no p = no λ { refl → p refl }
eq (a ⇒ a₁) U = no (λ ())
eq (a ⇒ a₁) P = no (λ ())
eq (a ⇒ a₁) (b ≈ b₁) = no (λ ())
eq U (b ⇒ b₁) = no (λ ())
eq U P = no (λ ())
eq P (var i) = no (λ ())
eq P (b $ b₁) = no (λ ())
eq P (λ' b) = no (λ ())
eq P (Π b b₁) = no (λ ())
eq P (b ⇒ b₁) = no (λ ())
eq P U = no (λ ())
eq P P = yes refl
eq P (b ≈ b₁) = no (λ ())
eq (a ≈ a₁) (b ⇒ b₁) = no (λ ())
eq (a ≈ a₁) P = no (λ ())