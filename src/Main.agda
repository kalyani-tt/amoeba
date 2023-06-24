{-# OPTIONS --guardedness #-}
module Main where

open import IO
import IO.Primitive as Prim
open import Core
open import Elab using(elab; ok; er; Error; error)
open import Parse using(runParse; parseSig; eof) renaming(_>>=_ to _p>>=_) renaming(_>>_ to _p>>_; pure to ppure)
open import Data.List using(List; []; _∷_)
open import Data.String using(String; _++_)
open import Function
open import Data.Product

postulate
    getArgs : Prim.IO (List String)
    readFile : String → Prim.IO String
    showNat : ℕ → String
{-# FOREIGN GHC
import qualified Data.Text as T
import System.Environment(getArgs) #-}
{-# COMPILE GHC getArgs = getArgs >>= \as -> pure (map T.pack as) #-}
{-# COMPILE GHC readFile = \name -> fmap T.pack (readFile (T.unpack name)) #-}
{-# COMPILE GHC showNat = T.pack . show #-}

showError : Error → String
showError (error line col msg) = showNat line ++ "." ++ showNat col ++ ": " ++ msg

main : Main
main = run do
    name ∷ _ ← lift getArgs where
        _ → putStrLn "No filename given"
    str ← lift (readFile name)
    ok ((γ , γi) , _) ← pure (runParse str (parseSig [] p>>= λ γ → eof p>> ppure γ)) where
        er err → putStrLn (showError err)
    ok _ ← pure (elab γ γi) where
        er err → putStrLn (showError err)
    putStrLn "All Ok."