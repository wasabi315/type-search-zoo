module Rittri89.NF where

open import Level using (Level; Lift) renaming (suc to ℓ-suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Rittri89.Type as Type using (Ctx⟦_⟧; _!_)

private
  variable
    ℓ : Level
    n : ℕ

infix  4 _⊆_
infixr 5 _`→_ _`→ᶠ_ _`→ⁿ_
infixr 6 _`×_ _∪_

--------------------------------------------------------------------------------

data Atom (n : ℕ) : Set
data Factor (n : ℕ) : Set
NF : (n : ℕ) → Set

data Atom n where
  var : (x : Fin n) → Atom n

data Factor n where
  _`→_ : (ν : NF n) (α : Atom n) → Factor n

NF n = List (Factor n)

pattern `⊤ = []
pattern _`×_ φ ν = φ ∷ ν

-- Smart constructors

record _⊆_ (T U : ℕ → Set) : Set where
  field
    ↑_ : T n → U n

open _⊆_ ⦃ ... ⦄ public

instance
  Atom⊆Factor : Atom ⊆ Factor
  Factor⊆NF   : Factor ⊆ NF
  Atom⊆NF     : Atom ⊆ NF

  Atom⊆Factor .↑_ α = `⊤ `→ α
  Factor⊆NF   .↑_ φ = φ `× `⊤
  Atom⊆NF     .↑_ α = (`⊤ `→ α) `× `⊤

_∪_ : (ν μ : NF n) → NF n
ν ∪ μ = ν ++ μ

_`→ᶠ_ : (ν : NF n) (φ : Factor n) → Factor n
ν `→ᶠ μ `→ α = ν ∪ μ `→ α

_`→ⁿ_ : (ν μ : NF n) → NF n
ν `→ⁿ μ = List.map (ν `→ᶠ_) μ

--------------------------------------------------------------------------------
-- Set interpretation

Atom⟦_⟧   : Atom n   → Ctx⟦ n ⟧ ℓ → Set ℓ
Factor⟦_⟧ : Factor n → Ctx⟦ n ⟧ ℓ → Set ℓ
NF⟦_⟧     : NF n     → Ctx⟦ n ⟧ ℓ → Set ℓ

Atom⟦ var x ⟧ ρ = ρ ! x

Factor⟦ ν `→ α ⟧ ρ = NF⟦ ν ⟧ ρ → Atom⟦ α ⟧ ρ

NF⟦ `⊤     ⟧ ρ = ⊤
NF⟦ φ `× ν ⟧ ρ = Factor⟦ φ ⟧ ρ × NF⟦ ν ⟧ ρ
