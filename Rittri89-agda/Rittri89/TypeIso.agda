module Rittri89.TypeIso where

open import Level using (Level) renaming (zero to ℓ-zero)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Algebra using (×-cong; ×-comm; ×-assoc; ×-identityˡ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Base using (_∘_)
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans)
open import Function.Properties using (→-cong-↔)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Structures using (IsEquivalence)

open import Rittri89.Type

private
  variable
    ℓ ℓ' : Level
    n : ℕ
    x y : Fin n
    A B C D : Type n

infix  4 _≅_
infixr 5 _`→_ _`→′_
infixr 6 _`×_ _`×′_

--------------------------------------------------------------------------------

data _≅_ {n} : (α β : Type n) → Set where
  -- Equivalence
  refl  : A ≅ A
  sym   : (A≅B : A ≅ B) → B ≅ A
  trans : (A≅B : A ≅ B) (B≅C : B ≅ C) → A ≅ C

  -- Congruence
  _`×_  : (A≅B : A ≅ B) (C≅D : C ≅ D) → A `× C ≅ B `× D
  _`→_  : (A≅B : A ≅ B) (C≅D : C ≅ D) → A `→ C ≅ B `→ D

  -- Axioms
  `×-comm        : ∀ A B → A `× B ≅ B `× A
  `×-assoc       : ∀ A B C → (A `× B) `× C ≅ A `× (B `× C)
  `→-curry       : ∀ A B C → A `→ (B `→ C) ≅ (A `× B) `→ C
  `→-distribˡ-`× : ∀ A B C → A `→ (B `× C) ≅ (A `→ B) `× (A `→ C)
  `×-identityˡ   : ∀ A → `⊤ `× A ≅ A
  `→-identityˡ   : ∀ A → `⊤ `→ A ≅ A
  `→-zeroʳ       : ∀ A → A `→ `⊤ ≅ `⊤

sym′   : A ≅ B → B ≅ A
sym′ refl            = refl
sym′ (sym A≅B)       = A≅B
sym′ (trans A≅B B≅C) = trans (sym′ B≅C) (sym′ A≅B)
sym′ (A≅B `× C≅D)    = sym′ A≅B `× sym′ C≅D
sym′ (A≅B `→ C≅D)    = sym′ A≅B `→ sym′ C≅D
sym′ A≅B             = sym A≅B

trans′ : A ≅ B → B ≅ C → A ≅ C
trans′ refl B≅C = B≅C
trans′ A≅B refl = A≅B
trans′ A≅B B≅C = trans A≅B B≅C

_`×′_ : A ≅ B → C ≅ D → A `× C ≅ B `× D
refl `×′ refl = refl
A≅B  `×′ C≅D  = A≅B `× C≅D

_`→′_ : A ≅ B → C ≅ D → A `→ C ≅ B `→ D
refl `→′ refl = refl
A≅B  `→′ C≅D  = A≅B `→ C≅D

isEquivalence : ∀ n → IsEquivalence (_≅_ {n = n})
isEquivalence n = record { refl = refl ; sym = sym′ ; trans = trans′ }

setoid : ℕ → Setoid ℓ-zero ℓ-zero
setoid n = record { _≈_ = _≅_ {n = n} ; isEquivalence = isEquivalence n }

`×-identityʳ : (A : Type n) → A `× `⊤ ≅ A
`×-identityʳ A = trans (`×-comm A `⊤) (`×-identityˡ A)

`×-swap : (A B C : Type n) → A `× B `× C ≅ B `× A `× C
`×-swap A B C = trans (sym (`×-assoc A B C)) (trans (`×-comm A B `× refl) (`×-assoc B A C))

--------------------------------------------------------------------------------
-- Interpretation into ↔

→-curry : ∀ {a b c} (A : Set a) (B : Set b) (C : Set c) →
          (A → (B → C)) ↔ ((A × B) → C)
→-curry A B C = mk↔ₛ′ (λ f → λ (x , y) → f x y) (λ f x y → f (x , y))
                      (λ _ → ≡.refl) (λ _ → ≡.refl)

-- η rules for × and → is enough to prove this.
→-distribˡ-× : ∀ {a b c} (A : Set a) (B : Set b) (C : Set c) →
               (A → (B × C)) ↔ ((A → B) × (A → C))
→-distribˡ-× A B C =
  mk↔ₛ′ (λ f → (proj₁ ∘ f) , (proj₂ ∘ f)) (λ (f , g) x → f x , g x)
        (λ _ → ≡.refl) (λ _ → ≡.refl)

-- η rules for ⊤ and → is enough to prove this.
→-identityˡ : (A : Set ℓ) → (⊤ {ℓ = ℓ'} → A) ↔ A
→-identityˡ A = mk↔ₛ′ (λ f → f tt) (λ x _ → x) (λ _ → ≡.refl) (λ _ → ≡.refl)

→-zeroʳ : (A : Set ℓ) → (A → ⊤ {ℓ = ℓ'}) ↔ ⊤
→-zeroʳ A = mk↔ₛ′ (λ _ → tt) (λ x _ → x) (λ _ → ≡.refl) (λ _ → ≡.refl)

-- Need extensionality for →-cong-↔ :(
module _ (ext : Extensionality ℓ ℓ) where

  ≅⟦_⟧ : {A B : Type n} → A ≅ B → (ρ : Ctx⟦ n ⟧ ℓ) → Type⟦ A ⟧ ρ ↔ Type⟦ B ⟧ ρ
  ≅⟦ refl                 ⟧ ρ = ↔-refl
  ≅⟦ sym A≅B              ⟧ ρ = ↔-sym (≅⟦ A≅B ⟧ ρ)
  ≅⟦ trans A≅B B≅C        ⟧ ρ = ↔-trans (≅⟦ A≅B ⟧ ρ) (≅⟦ B≅C ⟧ ρ)
  ≅⟦ A≅B `× C≅D           ⟧ ρ = ×-cong (≅⟦ A≅B ⟧ ρ) (≅⟦ C≅D ⟧ ρ)
  ≅⟦ A≅B `→ C≅D           ⟧ ρ = →-cong-↔ ext ext (≅⟦ A≅B ⟧ ρ) (≅⟦ C≅D ⟧ ρ)
  ≅⟦ `×-comm A B          ⟧ ρ = ×-comm (Type⟦ A ⟧ ρ) (Type⟦ B ⟧ ρ)
  ≅⟦ `×-assoc A B C       ⟧ ρ = ×-assoc _ (Type⟦ A ⟧ ρ) (Type⟦ B ⟧ ρ) (Type⟦ C ⟧ ρ)
  ≅⟦ `→-curry A B C       ⟧ ρ = →-curry (Type⟦ A ⟧ ρ) (Type⟦ B ⟧ ρ) (Type⟦ C ⟧ ρ)
  ≅⟦ `→-distribˡ-`× A B C ⟧ ρ = →-distribˡ-× (Type⟦ A ⟧ ρ) (Type⟦ B ⟧ ρ) (Type⟦ C ⟧ ρ)
  ≅⟦ `×-identityˡ A       ⟧ ρ = ×-identityˡ _ (Type⟦ A ⟧ ρ)
  ≅⟦ `→-identityˡ A       ⟧ ρ = →-identityˡ (Type⟦ A ⟧ ρ)
  ≅⟦ `→-zeroʳ A           ⟧ ρ = →-zeroʳ (Type⟦ A ⟧ ρ)
