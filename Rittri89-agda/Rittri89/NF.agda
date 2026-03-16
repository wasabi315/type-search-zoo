module Rittri89.NF where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ-syntax)
open import Function.Base using (flip)

private
  variable
    n : ℕ

infixr 5 _⇒_
infixr 6 _*_ _∷_

--------------------------------------------------------------------------------
-- Normal-form of types

data Sort : Set where
  atom factor product : Sort

private
  variable
    s : Sort

data NF (n : ℕ) : Sort → Set

Atom    = flip NF atom
Factor  = flip NF factor
Product = flip NF product

{-# DISPLAY NF n atom    = Atom n    #-}
{-# DISPLAY NF n factor  = Factor n  #-}
{-# DISPLAY NF n product = Product n #-}

data NF n where
  #_   : (x : Fin n) → Atom n
  list : (α : Product n) → Atom n

  _▶_  : (α : Product n) (β : Atom n) → Factor n

  unit : Product n
  _∷_  : (α : Factor n) (β : Product n) → Product n

NFScheme = Σ[ n ∈ ℕ ] Product n

--------------------------------------------------------------------------------

↑_ : Atom n → Factor n
↑ α = unit ▶ α

⇑_ : NF n s → Product n
⇑_ {s = atom}    α = ⇑ ↑ α
⇑_ {s = factor}  α = α ∷ unit
⇑_ {s = product} α = α

_*_ : NF n s → Product n → Product n
_*_ {s = atom}    α        βs = ↑ α ∷ βs
_*_ {s = factor}  α        βs = α ∷ βs
_*_ {s = product} unit     βs = βs
_*_ {s = product} (α ∷ αs) βs = α ∷ (αs * βs)

⇒-returnSort : Sort → Sort
⇒-returnSort atom    = factor
⇒-returnSort factor  = factor
⇒-returnSort product = product

_⇒_ : Product n → NF n s → NF n (⇒-returnSort s)
_⇒_ {s = atom}    αs β        = αs ▶ β
_⇒_ {s = factor}  αs (βs ▶ α) = (αs * βs) ▶ α
_⇒_ {s = product} αs unit     = unit
_⇒_ {s = product} αs (β ∷ βs) = (αs ⇒ β) ∷ (αs ⇒ βs)

length : Product n → ℕ
length unit    = 0
length (α ∷ β) = suc (length β)
