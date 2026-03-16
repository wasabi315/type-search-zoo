module Rittri89.Type where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ-syntax)

private
  variable
    n : ℕ

infixr 5 _⇒_
infixr 6 _*_

--------------------------------------------------------------------------------

data Type (n : ℕ) : Set where
  #_   : (x : Fin n) → Type n
  unit : Type n
  _*_  : (A B : Type n) → Type n
  _⇒_  : (A B : Type n) → Type n
  list : (A : Type n) → Type n

Scheme = Σ[ n ∈ ℕ ] Type n
