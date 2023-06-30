module Info where

open import Core
open import Data.Bool
open import Data.String using(String; _++_)
open import Data.List using(List; []; _∷_)

infixl 1 _◃_∶_

record TmInfo (a : Tm) : Set
data TmPartsInfo : Tm → Set
record SigInfo (γ : Sig) : Set
data SigPartsInfo : Sig → Set

record TmInfo a where
    inductive
    constructor tminfo
    field
        line col : ℕ
        parts : TmPartsInfo a

data TmPartsInfo where
    var : TmPartsInfo (var i)
    _$_ : TmInfo f → TmInfo a → TmPartsInfo (f $ a)
    λ' : String → TmInfo b → TmPartsInfo (λ' b)
    Π : String → TmInfo A → TmInfo B → TmPartsInfo (Π A B)
    U : TmPartsInfo U
    _≈_ : TmInfo a → TmInfo b → TmPartsInfo (a ≈ b)
    _⇒_ : TmInfo A → TmInfo B → TmPartsInfo (A ⇒ B)

record SigInfo γ where
    inductive
    constructor siginfo
    field
        line col : ℕ
        parts : SigPartsInfo γ

data SigPartsInfo where
    ∙ : SigPartsInfo ∙
    _◃_∶_ : TmInfo A → String → SigInfo γ → SigPartsInfo (A ◃ γ)

{-
no prec: var, U

-}

pretty : List String → Tm → String
pretty = help false where
    lookup : ℕ → List String → String
    lookup _ [] = "NOVAR"
    lookup zero (s ∷ _) = s
    lookup (suc i) (_ ∷ ss) = lookup i ss

    paren : Bool → String → String
    paren true s = "(" ++ s ++ ")"
    paren false s = s

    help : Bool → List String → Tm → String
    help p ss (var i) = lookup i ss
    help p ss (f $ a) = paren p (help false ss f ++ " " ++ help true ss a)
    help p ss (λ' b) = "\\x. " ++ help false ("x" ∷ ss) b
    help p ss (Π A B) = paren p ("(x : " ++ help true ss A ++ ") -> " ++ help false ("x" ∷ ss) B)
    help p ss U = "U"
    help p ss (a ≈ b) = paren p (help false ss a ++ " = " ++ help false ss b)
    help p ss (A ⇒ B) = paren p (help true ss A) ++ " => " ++ help false ss B