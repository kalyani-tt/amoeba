module Parse where

open import Core
open import Info
open import Elab renaming(_>>=_ to _e>>=_) hiding(_>>_; _<|>_)
open import Data.String using(String; fromList; toList; _++_) renaming(_≟_ to eqStr)
open import Data.Product hiding(map)
open import Data.List using(List; []; _∷_; reverse; foldr; foldl; map; filter) renaming(_++_ to _l++_)
open import Data.Char using(Char)
open import Agda.Builtin.Char
open import Data.Bool
open import Data.Unit
open import Data.Maybe using(Maybe; just; nothing) renaming(_>>=_ to _m>>=_)
open import Function hiding(_$_)

Token = ℕ × ℕ × String
Tokens = List Token

pattern tok line col s = (line , col , s)

isSep : Char → Bool
isSep ' ' = true
isSep '\\' = true
isSep '(' = true
isSep ')' = true
isSep _ = false

tokenize' : ℕ → ℕ → ℕ → List Char → Tokens → List Char → Tokens
tokenize' start line col ac as [] = (line , col , fromList (reverse ac)) ∷ as
tokenize' start line col ac as ('\n' ∷ cs) = tokenize' 0 (suc line) 0 [] ((line , start , fromList (reverse ac)) ∷ as) cs
tokenize' start line col ac as (c ∷ cs) with isSep c
... | true = tokenize' (suc col) line (suc col) [] ((line , col , fromList (c ∷ [])) ∷ (line , start , fromList (reverse ac)) ∷ as) cs
... | false = tokenize' start line (suc col) (c ∷ ac) as cs

or : Bool → Bool → Bool
or true _ = true
or _ b = b

bl : {a b : String} → Dec (a ≡ b) → Bool
bl (yes _) = true
bl (no _) = false

strip : Tokens → Tokens
strip [] = []
strip (tok line col s ∷ ts) with or (bl (eqStr s "")) (bl (eqStr s " "))
... | true = strip ts
... | false = tok line col s ∷ strip ts

tokenize : String → Tokens
tokenize s = strip (reverse (tokenize' 0 0 0 [] [] (toList s)))

Parse : Set → Set
Parse A = Tokens → Elab (A × Tokens) 

runParse : ∀{A} → String → Parse A → Elab (A × Tokens)
runParse s p = p (tokenize s)

pure : ∀{A} → A → Parse A
pure x ts = ok (x , ts)

per : ∀{A} → Error → Parse A
per e _ = er e

_>>=_ : ∀{A B} → Parse A → (A → Parse B) → Parse B
(p >>= k) ts₁ = p ts₁ e>>= λ (x , ts₂) → k x ts₂

_>>_ : ∀{A B} → Parse A → Parse B → Parse B
p₁ >> p₂ = p₁ >>= λ _ → p₂

infixr 20 _<|>_
_<|>_ : ∀{A} → Parse A → Parse A → Parse A
(p₁ <|> p₂) ts with p₁ ts
... | ok x = ok x
... | er _ = p₂ ts

eofErr : ∀{A} → Elab A
eofErr = er (error 0 0 "End of input")

expect : String → Parse ⊤
expect s (tok line col t ∷ ts) with eqStr s t
... | yes refl = ok (tt , ts)
... | no _ = er (error line col ("Expected a '" ++ s ++ "', got a '" ++ t ++ "'"))
expect s [] = er (error 0 0 ("Expected a '" ++ s ++ "', got EOF"))

single : Parse String
single (tok _ _ t ∷ ts) = ok (t , ts)
single [] = eofErr

lookupName : String → List String → Maybe ℕ
lookupName s (n ∷ ss) with eqStr n s
... | yes refl = just 0
... | no _ = lookupName s ss m>>= just ∘ suc
lookupName _ [] = nothing

loc : Parse (ℕ × ℕ)
loc ts@(tok line col _ ∷ _) = ok ((line , col) , ts)
loc [] = eofErr

notNext : String → Parse ⊤
notNext s ts@(tok line col t ∷ _) with eqStr s t
... | yes refl = er (error line col ("Expected not a '" ++ s ++ "'"))
... | no _ = ok (tt , ts)
notNext s [] = ok (tt , [])

eof : Parse ⊤
eof [] = ok (tt , [])
eof _ = er (error 0 0 "Not EOF")

ParseTm = Scope → Parse (∃[ a ] TmInfo a)

{-# NON_TERMINATING #-}
many : ∀{A} → Parse A → Parse (List A)
many p =
    (do
        x ← p
        xs ← many p
        pure (x ∷ xs)) <|>
    pure []

{-# NON_TERMINATING #-}
prec0 : ParseTm 

lams : TmInfo b → (names : List (ℕ × ℕ × String)) → TmInfo (foldr (λ _ → λ') b names)
lams bi [] = bi
lams bi ((line , col , name) ∷ names) = tminfo line col (λ' name (lams bi names))

apps : TmInfo f → (args : List (∃[ a ] TmInfo a)) → TmInfo (foldr (λ (a , _) acc → acc $ a) f args)
apps fi [] = fi
apps fi ((_ , ai) ∷ as) = tminfo 0 0 (apps fi as $ ai)

prec2 : ParseTm
prec2 ss =
    (do
        line , col ← loc
        expect "Type"
        pure (U , tminfo line col U)) <|>
    (do
        line , col ← loc
        name ← single
        just i ← pure (lookupName name ss) where
            nothing → per (error line col ("No variable '" ++ name ++ "' in scope"))
        pure (var i , tminfo line col var)) <|>
    (do
        expect "\\"
        names ← many do
            line , col ← loc
            notNext "."
            name ← single
            pure (line , col , name)
        expect "."
        b , bi ← prec0 (reverse (map (proj₂ ∘ proj₂) names) l++ ss)
        pure (foldr (λ _ → λ') b names , lams bi names)) <|>
    (do
        line , col ← loc
        expect "("
        name ← single
        expect ":"
        A , Ai ← prec0 ss
        expect ")"
        expect "->"
        B , Bi ← prec0 (name ∷ ss)
        pure (Π A B , tminfo line col (Π name Ai Bi))) <|>
    (do
        expect "("
        x ← prec0 ss
        expect ")"
        pure x)

prec1 : ParseTm
prec1 ss = do
    line , col ← loc
    f , fi ← prec2 ss
    as ← many (prec2 ss)
    let as = reverse as
    pure (foldr (λ (a , _) acc → acc $ a) f as , apps fi as)

prec0 ss =
    (do
        line , col ← loc
        a , ai ← prec1 ss
        expect "="
        b , bi ← prec1 ss
        pure ((a ≈ b) , tminfo line col (ai ≈ bi))) <|>
    (do
        line , col ← loc
        A , Ai ← prec1 ss
        expect "->"
        B , Bi ← prec0 ("_" ∷ ss)
        pure (Π A B , tminfo line col (Π "_" Ai Bi))) <|>
    (do
        line , col ← loc
        A , Ai ← prec1 ss
        expect "=>"
        B , Bi ← prec0 ss
        pure ((A ⇒ B) , tminfo line col (Ai ⇒ Bi))) <|>
    prec1 ss

{-# NON_TERMINATING #-}
parseSig : Scope → Parse (∃[ γ ] SigInfo γ)
parseSig ss =
    (do
        line , col ← loc
        name ← single
        expect ":"
        A , Ai ← prec0 ss
        γ , γi ← parseSig (name ∷ ss)
        pure ((A ◃ γ) , siginfo line col (Ai ◃ name ∶ γi))) <|>
    (do
        pure (∙ , siginfo zero zero ∙))