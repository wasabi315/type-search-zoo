module Rittri89.TypeIso where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import Rittri89.Type

private
  variable
    n : ℕ
    x y : Fin n
    A B C A′ B′ C′ D : Type n

infix  4 _≅_
infixr 5 _⇒_ _⇒′_
infixr 6 _*_ _*′_

--------------------------------------------------------------------------------

data _≅_ {n} : (α β : Type n) → Set where
  -- Equivalence
  refl  : A ≅ A
  sym   : (p : A ≅ B) → B ≅ A
  trans : (p : A ≅ B) (q : B ≅ C) → A ≅ C

  -- Congruence
  _*_ : (p : A ≅ B) (q : C ≅ D) → A * C ≅ B * D
  _⇒_ : (p : A ≅ B) (q : C ≅ D) → A ⇒ C ≅ B ⇒ D
  list : (p : A ≅ B) → list A ≅ list B

  -- Axioms
  *-identityˡ : unit * A ≅ A
  *-comm      : A * B ≅ B * A
  *-assoc     : (A * B) * C ≅ A * (B * C)

  ⇒-identityˡ : A ≅ unit ⇒ A
  uncurry     : A ⇒ (B ⇒ C) ≅ (A * B) ⇒ C

  ⇒-zeroʳ     : A ⇒ unit ≅ unit
  distrib     : A ⇒ (B * C) ≅ (A ⇒ B) * (A ⇒ C)

pattern _*- {n} {A} {B} {C} p = _*_ {n} {A} {B} p (refl {C})
pattern -*_ {n} {A} {B} {C} p = _*_ {n} {C = B} {D = C} (refl {A}) p
pattern _⇒- {n} {A} {B} {C} p = _⇒_ {n} {A} {B} p (refl {C})
pattern -⇒_ {n} {A} {B} {C} p = _⇒_ {n} {C = B} {D = C} (refl {A}) p

sym′ : A ≅ B → B ≅ A
sym′ refl    = refl
sym′ (sym p) = p
sym′ p       = sym p

trans′ : A ≅ B → B ≅ C → A ≅ C
trans′ refl q    = q
trans′ p    refl = p
trans′ p    q    = trans p q

_*′_ : A ≅ B → C ≅ D → A * C ≅ B * D
refl *′ refl = refl
p    *′ q    = p * q

_⇒′_ : A ≅ B → C ≅ D → A ⇒ C ≅ B ⇒ D
refl ⇒′ refl = refl
p    ⇒′ q    = p ⇒ q

list′ : A ≅ B → list A ≅ list B
list′ refl = refl
list′ p    = list p

--------------------------------------------------------------------------------

*-identityʳ : A * unit ≅ A
*-identityʳ = trans *-comm *-identityˡ

*-swap : A ≅ A′ → B ≅ B′ → C ≅ C′ → A * B * C ≅ B′ * A′ * C′
*-swap p q r = trans′ (p *′ q *′ r) (trans (sym *-assoc) (trans (*-comm *-) *-assoc))

--------------------------------------------------------------------------------

isEquivalence : ∀ n → IsEquivalence (_≅_ {n})
isEquivalence n = record { refl = refl ; sym = sym′ ; trans = trans′ }

setoid : ℕ → Setoid _ _
setoid n = record { isEquivalence = isEquivalence n }
