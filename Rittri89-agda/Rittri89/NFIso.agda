module Rittri89.NFIso where

open import Level using (Level) renaming (zero to ℓ-zero)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as Fin
open import Data.Nat.Base using (ℕ)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Data.List.Relation.Binary.Permutation.Homogeneous as ↭
import Data.List.Relation.Binary.Pointwise as =̇
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Product.Algebra using (×-cong; ×-comm; ×-assoc; ×-identityˡ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans)
open import Function.Properties using (→-cong-↔)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; _×-dec_; no)

open import Rittri89.Type using (Ctx⟦_⟧)
open import Rittri89.TypeIso using (List-cong)
open import Rittri89.NF

private
  variable
    ℓ ℓ' : Level
    n : ℕ
    x y : Fin n
    α β γ : Atom n
    ε φ ψ θ : Factor n
    ν μ ι σ τ : NF n

infix  4 _≅ᵃ_ _≅ᶠ_ _≟ᵃ_ _≟ᶠ_
infixr 5 _`→_

--------------------------------------------------------------------------------

data _≅ᵃ_ {n} : (α β : Atom n) → Set
data _≅ᶠ_ {n} : (φ ψ : Factor n) → Set

_≟ᵃ_ : (α β : Atom n) → Dec (α ≅ᵃ β)
_≟ᶠ_ : (φ ψ : Factor n) → Dec (φ ≅ᶠ ψ)

{-# TERMINATING #-} -- Uh oh
isEquivalenceᵃ : ∀ n → IsEquivalence (_≅ᵃ_ {n = n})
isEquivalenceᶠ : ∀ n → IsEquivalence (_≅ᶠ_ {n = n})

isDecEquivalenceᵃ : ∀ n → IsDecEquivalence (_≅ᵃ_ {n = n})
isDecEquivalenceᶠ : ∀ n → IsDecEquivalence (_≅ᶠ_ {n = n})

isDecEquivalenceᵃ n = record { isEquivalence = isEquivalenceᵃ n ; _≟_ = _≟ᵃ_ }
isDecEquivalenceᶠ n = record { isEquivalence = isEquivalenceᶠ n ; _≟_ = _≟ᶠ_ }

decSetoidᵃ : ℕ → DecSetoid ℓ-zero ℓ-zero
decSetoidᵃ n = record { _≈_ = _≅ᵃ_ ; isDecEquivalence = isDecEquivalenceᵃ n }

decSetoidᶠ : ℕ → DecSetoid ℓ-zero ℓ-zero
decSetoidᶠ n = record { _≈_ = _≅ᶠ_ ; isDecEquivalence = isDecEquivalenceᶠ n }

module _ {n : ℕ} where
  import Data.List.Relation.Binary.Permutation.Setoid (DecSetoid.setoid (decSetoidᶠ n)) as Permutation
  open Permutation public
    using ()
    renaming (_↭_ to infix 4 _≅ⁿ_;
              ↭-refl to reflⁿ; ↭-reflexive to reflexiveⁿ; ↭-sym to symⁿ; ↭-trans to transⁿ;
              ↭-swap to swapⁿ)
  open import Data.List.Relation.Binary.Permutation.Setoid.Properties (DecSetoid.setoid (decSetoidᶠ n)) public
    using ()
    renaming (++⁺ to ∪-cong; ++-comm to ∪-comm)

  infixr 6 _`×_ _`×′_

  pattern _`×_ φ≅ψ ν≅μ = Permutation.prep φ≅ψ ν≅μ

  _`×′_ : φ ≅ᶠ ψ → ν ≅ⁿ μ → φ `× ν ≅ⁿ ψ `× μ
  _`×′_ = _`×_

isEquivalenceⁿ : ∀ n → IsEquivalence (_≅ⁿ_ {n = n})
isEquivalenceⁿ n = record { refl = reflⁿ ; sym = symⁿ ; trans = transⁿ }

data _≅ᵃ_ where
  var   : (x≡y : x ≡ y) → var x ≅ᵃ var y
  `List : (ν≅μ : ν ≅ⁿ μ) → `List ν ≅ᵃ `List μ

data _≅ᶠ_ where
  _`→_ : (ν≅μ : ν ≅ⁿ μ) (α≅β : α ≅ᵃ β) → ν `→ α ≅ᶠ μ `→ β

reflᵃ : α ≅ᵃ α
reflᶠ : φ ≅ᶠ φ

reflᵃ {α = var x}   = var ≡.refl
reflᵃ {α = `List ν} = `List reflⁿ
reflᶠ {φ = ν `→ α}  = reflⁿ `→ reflᵃ

symᵃ : α ≅ᵃ β → β ≅ᵃ α
symᶠ : φ ≅ᶠ ψ → ψ ≅ᶠ φ

symᵃ (var x≡y)    = var (≡.sym x≡y)
symᵃ (`List ν≅μ)  = `List (symⁿ ν≅μ)
symᶠ (ν≅μ `→ α≅β) = symⁿ ν≅μ `→ symᵃ α≅β

transᵃ : α ≅ᵃ β → β ≅ᵃ γ → α ≅ᵃ γ
transᶠ : {φ ψ θ : Factor n} → φ ≅ᶠ ψ → ψ ≅ᶠ θ → φ ≅ᶠ θ

transᵃ (var x≡y)    (var y≡z)    = var (≡.trans x≡y y≡z)
transᵃ (`List ν≅μ)  (`List μ≅ι)  = `List (transⁿ ν≅μ μ≅ι)
transᶠ (ν≅μ `→ α≅β) (ρ≅σ `→ β≅γ) = transⁿ ν≅μ ρ≅σ `→ transᵃ α≅β β≅γ

isEquivalenceᵃ n = record { refl = reflᵃ ; sym = symᵃ ; trans = transᵃ }
isEquivalenceᶠ n = record { refl = reflᶠ ; sym = symᶠ ; trans = transᶠ }

var-injective : var x ≅ᵃ var y → x ≡ y
var-injective (var x≡y) = x≡y

`List-injective : `List ν ≅ᵃ `List μ → ν ≅ⁿ μ
`List-injective (`List ν≅μ) = ν≅μ

`→-injective : ν `→ α ≅ᶠ μ `→ β → ν ≅ⁿ μ × α ≅ᵃ β
`→-injective (ν≅μ `→ α≅β) = ν≅μ , α≅β

-- Up to propositional equality
∪-identityʳ : (ν : NF n) → ν ∪ `⊤ ≡ ν
∪-identityʳ = ++-identityʳ

-- Up to propositional equality
∪-assoc : (ν μ ι : NF n) → (ν ∪ μ) ∪ ι ≡ ν ∪ (μ ∪ ι)
∪-assoc = ++-assoc

`→ᶠ-cong : ν ≅ⁿ μ → φ ≅ᶠ ψ → ν `→ᶠ φ ≅ᶠ μ `→ᶠ ψ
`→ᶠ-cong ν≅μ (ι≅σ `→ α≅β) = ∪-cong ν≅μ ι≅σ `→ α≅β

`→ⁿ-cong : ν ≅ⁿ μ → ι ≅ⁿ σ → ν `→ⁿ ι ≅ⁿ μ `→ⁿ σ
`→ⁿ-cong ν≅μ (↭.refl ι≋σ)         = =̇.rec (λ {ι} {σ} _ → _ `→ⁿ ι ≅ⁿ _ `→ⁿ σ) (λ φ≅ψ → ↭.prep (`→ᶠ-cong ν≅μ φ≅ψ)) reflⁿ ι≋σ
`→ⁿ-cong ν≅μ (↭.prep φ≅ψ ι≅σ)     = ↭.prep (`→ᶠ-cong ν≅μ φ≅ψ) (`→ⁿ-cong ν≅μ ι≅σ)
`→ⁿ-cong ν≅μ (↭.swap φ≅ψ ε≅θ ι≅σ) = ↭.trans (↭.prep (`→ᶠ-cong ν≅μ φ≅ψ) (↭.prep (`→ᶠ-cong ν≅μ ε≅θ) (`→ⁿ-cong ν≅μ ι≅σ))) (↭.swap reflᶠ reflᶠ reflⁿ)
`→ⁿ-cong ν≅μ (↭.trans ι≅σ σ≅τ)    = ↭.trans (`→ⁿ-cong ν≅μ ι≅σ) (`→ⁿ-cong reflⁿ σ≅τ)

`→ᶠ-identityˡ : (φ : Factor n) → `⊤ `→ᶠ φ ≅ᶠ φ
`→ᶠ-identityˡ (ν `→ α) = reflᶠ

`→ⁿ-identityˡ : (ν : NF n) → `⊤ `→ⁿ ν ≅ⁿ ν
`→ⁿ-identityˡ `⊤       = reflⁿ
`→ⁿ-identityˡ (φ `× ν) = `→ᶠ-identityˡ φ `×′ `→ⁿ-identityˡ ν

`→ᶠ-curry : (ν μ : NF n) (φ : Factor n) → ν `→ᶠ (μ `→ᶠ φ) ≅ᶠ (ν ∪ μ) `→ᶠ φ
`→ᶠ-curry ν μ (ι `→ α) = reflexiveⁿ (≡.sym (∪-assoc ν μ ι)) `→ reflᵃ

`→ⁿ-curry : (ν μ ι : NF n) → ν `→ⁿ (μ `→ⁿ ι) ≅ⁿ (ν ∪ μ) `→ⁿ ι
`→ⁿ-curry ν μ `⊤       = reflⁿ
`→ⁿ-curry ν μ (φ `× ι) = `→ᶠ-curry ν μ φ `×′ `→ⁿ-curry ν μ ι

`→ⁿ-distribˡ-∪ : (ν μ ι : NF n) → ν `→ⁿ (μ ∪ ι) ≅ⁿ (ν `→ⁿ μ) ∪ (ν `→ⁿ ι)
`→ⁿ-distribˡ-∪ ν `⊤       ι = reflⁿ
`→ⁿ-distribˡ-∪ ν (φ `× μ) ι = reflᶠ `×′ `→ⁿ-distribˡ-∪ ν μ ι

--------------------------------------------------------------------------------
-- Decision procedure

module _ {n : ℕ} where
  open import Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure (decSetoidᶠ n) public
    using ()
    renaming (permutation? to infix 4 _≟ⁿ_)

var x   ≟ᵃ var y   = Dec.map′ var var-injective (x Fin.≟ y)
`List ν ≟ᵃ `List μ = Dec.map′ `List `List-injective (ν ≟ⁿ μ)
var x   ≟ᵃ `List ν = no λ ()
`List ν ≟ᵃ var x   = no λ ()

ν `→ α ≟ᶠ μ `→ β = Dec.map′ (uncurry _`→_) `→-injective (ν ≟ⁿ μ ×-dec α ≟ᵃ β)

isDecEquivalenceⁿ : ∀ n → IsDecEquivalence (_≅ⁿ_ {n = n})
isDecEquivalenceⁿ n = record { isEquivalence = isEquivalenceⁿ n ; _≟_ = _≟ⁿ_ }

decSetoidⁿ : ℕ → DecSetoid ℓ-zero ℓ-zero
decSetoidⁿ n = record { _≈_ = _≅ⁿ_ ; isDecEquivalence = isDecEquivalenceⁿ n }

--------------------------------------------------------------------------------
-- Interpretation into ↔

×-swap : ∀ {a b c} (A : Set a) (B : Set b) (C : Set c) →
         (A × B × C) ↔ (B × A × C)
×-swap A B C = mk↔ₛ′ (λ (x , y , z) → y , x , z) (λ (y , x , z) → x , y , z)
                     (λ _ → ≡.refl) (λ _ → ≡.refl)

-- Need extensionality for →-cong-↔ :(
module _ (ext : Extensionality ℓ ℓ) where

  {-# TERMINATING #-} -- Uh oh
  ≅ᵃ⟦_⟧ : {α β : Atom n} → α ≅ᵃ β → (ρ : Ctx⟦ n ⟧ ℓ) → Atom⟦ α ⟧ ρ ↔ Atom⟦ β ⟧ ρ
  ≅ᶠ⟦_⟧ : {φ ψ : Factor n} → φ ≅ᶠ ψ → (ρ : Ctx⟦ n ⟧ ℓ) → Factor⟦ φ ⟧ ρ ↔ Factor⟦ ψ ⟧ ρ
  ≅ⁿ⟦_⟧ : {ν μ : NF n} → ν ≅ⁿ μ → (ρ : Ctx⟦ n ⟧ ℓ) → NF⟦ ν ⟧ ρ ↔ NF⟦ μ ⟧ ρ

  ≅ᵃ⟦ var ≡.refl ⟧ ρ = ↔-refl
  ≅ᵃ⟦ `List ν≅μ  ⟧ ρ = List-cong (≅ⁿ⟦ ν≅μ ⟧ ρ)

  ≅ᶠ⟦ ν≅μ `→ α≅β ⟧ ρ = →-cong-↔ ext ext (≅ⁿ⟦ ν≅μ ⟧ ρ) (≅ᵃ⟦ α≅β ⟧ ρ)

  ≅ⁿ⟦ ↭.refl ν≋μ         ⟧ ρ = =̇.rec (λ {ν} {μ} _ → NF⟦ ν ⟧ ρ ↔ NF⟦ μ ⟧ ρ) (λ φ≋ψ → ×-cong (≅ᶠ⟦ φ≋ψ ⟧ ρ)) ↔-refl ν≋μ
  ≅ⁿ⟦ ↭.prep φ≋ψ ν≋μ     ⟧ ρ = ×-cong (≅ᶠ⟦ φ≋ψ ⟧ ρ) (≅ⁿ⟦ ν≋μ ⟧ ρ)
  ≅ⁿ⟦ ↭.swap φ≋ψ ε≅θ ν≋μ ⟧ ρ = ↔-trans (×-cong (≅ᶠ⟦ φ≋ψ ⟧ ρ) (×-cong (≅ᶠ⟦ ε≅θ ⟧ ρ) (≅ⁿ⟦ ν≋μ ⟧ ρ))) (×-swap _ _ _)
  ≅ⁿ⟦ ↭.trans ν≋μ μ≋ι    ⟧ ρ = ↔-trans (≅ⁿ⟦ ν≋μ ⟧ ρ) (≅ⁿ⟦ μ≋ι ⟧ ρ)
