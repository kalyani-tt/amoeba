module Elab where

open import Core
open import Norm
open import Data.Sum as Sum
open import Data.String hiding(_≈_) renaming(_≟_ to eqStr)
open import Data.Product
open import Data.Unit
open import Data.List hiding(_++_)
open import Function using(id; case_of_)
open import Data.Maybe using(Maybe; just; nothing)
open import Data.Maybe as Maybe

Error = String
Name = String

data Mode : Set where
    chk inf : Mode

record State : Set where
    constructor state
    field
        bindings : List Name
open State

withName : Name → State → State
withName v s = record s { bindings = v ∷ bindings s }

catNames : List Name → String
catNames [] = ""
catNames (v ∷ []) = v
catNames (v ∷ vs) = v ++ " " ++ catNames vs

modeInp : Ctx → Mode → Set
modeInp Γ chk = Ty
modeInp Γ inf = ⊤

modeOut : (Γ : Ctx) (m : Mode) → modeInp Γ m → Set
modeOut Γ chk A = ∃[ a ] (Γ ⊢ a ∶ A)
modeOut Γ inf tt = ∃[ a ] ∃[ A ] (Γ ⊢ a ∶ A)

Elab : Mode → Set
Elab m = State → ∀ Γ (inp : modeInp Γ m) → String × modeOut Γ m inp

run : ∀ A → Elab chk → String × modeOut ∙ chk A
run A ea = ea (state []) ∙ A

er : ∀ Γ m inp → String → String × modeOut Γ m inp
er Γ chk inp e = "[ " ++ e ++ " ]" , hole , tp-hole
er Γ inf inp e = "[ " ++ e ++ " ]" , hole , hole , tp-hole

admit : Elab chk
admit s Γ A = "[?]" , hole , tp-hole

switch : Elab inf → Elab chk
switch ea s Γ A =
    let da , a , B , tp-a = ea s Γ tt
    in case (norm Γ A , norm Γ B) of λ
        { (just (C , A≈C) , just (D , D≈B)) →
            case eq C D of λ
             { (yes refl) → da , a , conv (≈sym (≈trans A≈C (≈sym D≈B))) tp-a
             ; (no _) → er Γ chk A "Types not equal"}
        ; _ → er Γ chk A "Failed to normalize" }

intros : List Name → Elab chk → Elab chk
intros vs = help ("λ" ++ catNames vs) vs where
    help : String → List Name → Elab chk → Elab chk
    help acc [] eb s Γ B =
        let db , b , tp-b = eb s Γ B
        in (acc ++ ". " ++ db) , b , tp-b
    help acc (v ∷ vs) eb s Γ (Π A B) =
        let db , b , tp-b = help acc vs eb (withName v s) (shfCtx (Γ ◂ A)) B
        in db , λ' b , tp-λ tp-b
    help acc (_ ∷ _) _ _ Γ G = er Γ chk G "Not a Π"

getIndex : Name → List Name → Maybe ℕ
getIndex v [] = nothing
getIndex v (v' ∷ vs) with eqStr v v'
... | yes refl = just 0
... | no _ = Maybe.map suc (getIndex v vs)

fetch : ∀ Γ i → Maybe (∃[ A ] (i ∶ A ∈ Γ))
fetch ∙ i = nothing
fetch (Γ ◂ A) zero = just (A , here)
fetch (Γ ◂ A) (suc i) = Maybe.map (λ (A ,  i∈Γ) → A , there i∈Γ) (fetch Γ i)

hyp : Name → Elab inf
hyp v s Γ tt with getIndex v (bindings s)
hyp v s Γ tt | just i with fetch Γ i
hyp v s Γ tt | just i | just (A , i∈Γ) = v , var i , A , tp-var i∈Γ
hyp v s Γ tt | just i | nothing = er Γ inf tt "Bug in fetch"
hyp v s Γ tt | nothing = er Γ inf tt ("No such variable " ++ v)

pis : List Name → Elab chk → Elab chk → Elab chk
pis vs eA eB s Γ G =
    let dA , _ = eA s Γ G
    in (help (λ dB → "Π " ++ catNames vs ++ " : " ++ dA ++ ". " ++ dB) vs eA eB) s Γ G
  where
    help : (String → String) → List Name → Elab chk → Elab chk → Elab chk
    help acc [] eA eB s Γ G =
        let dB , B , tp-B = eB s Γ G
        in acc dB , B , tp-B
    help acc (v ∷ vs) eA eB s Γ U =
        let _ , A , tp-A = eA s Γ U
            dB , B , tp-B = help acc vs eA eB (withName v s) (shfCtx (Γ ◂ A)) U
        in dB , Π A B , tp-Π tp-A tp-B
    help acc _ _ _ _ Γ G = er Γ chk G "Not a U"

arr : Elab chk → Elab chk → Elab chk
arr eA eB s Γ U =
    let dA , A , tp-A = eA s Γ U
        dB , B , tp-B = eB (withName "_" s) (shfCtx (Γ ◂ A)) U
    in (dA ++ " → " ++ dB) , Π A B , tp-Π tp-A tp-B
arr _ _ _ Γ G = er Γ chk G "Not a U"

type : Elab chk
type s Γ U = "Type" , U , tp-U
type _ Γ G = er Γ chk G "Not a U"

qed : Elab chk
qed s Γ U = "" , U , tp-U
qed _ Γ G = er Γ chk G "Not a U"

definition : Name → Elab chk → Elab chk → Elab chk → Elab chk
definition v eA ea eB s Γ U =
    let dA , A , tp-A = eA s Γ U
        da , a , tp-a = ea s Γ A
        dB , B , tp-B = eB (withName "_" (withName v s)) (shfCtx (shfCtx (Γ ◂ A) ◂ (var 0 ≈ shf a))) U
    in v ++ " : " ++ dA ++ "\n" ++ v ++ " ≔ " ++ da ++ "\n\n" ++ dB ,
        Π A (Π (var 0 ≈ shf a) B) ,
        tp-Π tp-A (tp-Π (tp-≈ (tp-var here) (tp-shf {B = A} tp-a)) tp-B)
definition _ _ _ _ _ Γ G = er Γ chk G "Not a U"