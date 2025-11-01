module Rittri89.Type where

open import Level using (Level; Lift) renaming (suc to ℓ-suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)

private
  variable
    ℓ : Level
    n : ℕ

infixr 5 _`→_
infixr 6 _`×_

--------------------------------------------------------------------------------

data Type (n : ℕ) : Set where
  var   : (x : Fin n) → Type n
  `⊤    : Type n
  _`×_  : (A B : Type n) → Type n
  _`→_  : (A B : Type n) → Type n

--------------------------------------------------------------------------------
-- Set interpretation

Ctx⟦_⟧ : ℕ → ∀ ℓ → Set (ℓ-suc ℓ)
Ctx⟦ zero  ⟧ ℓ = ⊤
Ctx⟦ suc n ⟧ ℓ = Ctx⟦ n ⟧ ℓ × Set ℓ

_!_ : Ctx⟦ n ⟧ ℓ → Fin n → Set ℓ
_!_ {suc n} (ρ , A) zero    = A
_!_ {suc n} (ρ , A) (suc x) = ρ ! x

Type⟦_⟧ : Type n → Ctx⟦ n ⟧ ℓ → Set ℓ
Type⟦ var x   ⟧ ρ = ρ ! x
Type⟦ `⊤      ⟧ ρ = ⊤
Type⟦ α `× β  ⟧ ρ = Type⟦ α ⟧ ρ × Type⟦ β ⟧ ρ
Type⟦ α `→ β  ⟧ ρ = Type⟦ α ⟧ ρ → Type⟦ β ⟧ ρ
