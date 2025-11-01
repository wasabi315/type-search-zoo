module Rittri89.Normalise where

open import Level using (Level)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Core using (_Preserves_⟶_)
import Data.List.Relation.Binary.Permutation.Homogeneous as ↭
import Data.List.Relation.Binary.Pointwise as =̇
open import Function.Base using (flip)
open import Function.Bundles using (Inverse; _↔_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes; no)
open import Tactic.Cong using (cong!; ⌞_⌟)

open import Rittri89.NF as NF using (Atom; Factor; NF; ↑_)
open import Rittri89.Type as Type using (Type; Type⟦_⟧; Ctx⟦_⟧)
open import Rittri89.TypeIso as Iso using (_≅_; ≅⟦_⟧)
open import Rittri89.NFIso as NFIso using (_≅ᵃ_; _≅ᶠ_; _≅ⁿ_; ↑↑_)

private
  variable
    ℓ : Level
    n : ℕ
    x y : Fin n
    A B C : Type n
    α β γ : Atom n
    ε φ ψ θ : Factor n
    ν μ ι : NF n

infix 4 _≟_

--------------------------------------------------------------------------------

normalise : Type n → NF n
normalise (Type.var x)  = ↑ Atom.var x
normalise Type.`⊤       = NF.`⊤
normalise (A Type.`× B) = normalise A NF.∪ normalise B
normalise (A Type.`→ B) = normalise A NF.`→ⁿ normalise B

quoteᵃ : Atom n → Type n
quoteᶠ : Factor n → Type n
quoteⁿ : NF n → Type n

quoteᵃ (Atom.var x)    = Type.var x
quoteᶠ (ν Factor.`→ α) = quoteⁿ ν Type.`→ quoteᵃ α
quoteⁿ NF.`⊤           = Type.`⊤
quoteⁿ (φ NF.`× ν)     = quoteᶠ φ Type.`× quoteⁿ ν

--------------------------------------------------------------------------------

normalise-pres-≅ : normalise {n = n} Preserves _≅_ ⟶ _≅ⁿ_
normalise-pres-≅ Iso.refl = NFIso.reflⁿ
normalise-pres-≅ (Iso.sym A≅B) = NFIso.symⁿ (normalise-pres-≅ A≅B)
normalise-pres-≅ (Iso.trans A≅B B≅C) = NFIso.transⁿ (normalise-pres-≅ A≅B) (normalise-pres-≅ B≅C)
normalise-pres-≅ (A≅B Iso.`× C≅D) = NFIso.∪-cong (normalise-pres-≅ A≅B) (normalise-pres-≅ C≅D)
normalise-pres-≅ (A≅B Iso.`→ B≅C) = NFIso.`→ⁿ-cong (normalise-pres-≅ A≅B) (normalise-pres-≅ B≅C)
normalise-pres-≅ (Iso.`×-comm A B) = NFIso.∪-comm (normalise A) (normalise B)
normalise-pres-≅ (Iso.`×-assoc A B C) = NFIso.reflexiveⁿ (NFIso.∪-assoc (normalise A) (normalise B) (normalise C))
normalise-pres-≅ (Iso.`→-curry A B C) = NFIso.`→ⁿ-curry (normalise A) (normalise B) (normalise C)
normalise-pres-≅ (Iso.`→-distribˡ-`× A B C) = NFIso.`→ⁿ-distribˡ-∪ (normalise A) (normalise B) (normalise C)
normalise-pres-≅ (Iso.`×-identityˡ A) = NFIso.reflⁿ
normalise-pres-≅ (Iso.`→-identityˡ A) = NFIso.`→ⁿ-identityˡ (normalise A)
normalise-pres-≅ (Iso.`→-zeroʳ A) = NFIso.reflⁿ

{-# TERMINATING #-}
quoteᵃ-pres-≅ : quoteᵃ {n = n} Preserves _≅ᵃ_ ⟶ _≅_
quoteᶠ-pres-≅ : quoteᶠ {n = n} Preserves _≅ᶠ_ ⟶ _≅_
quoteⁿ-pres-≅ : quoteⁿ {n = n} Preserves _≅ⁿ_ ⟶ _≅_

quoteᵃ-pres-≅ (NFIso.var ≡.refl)   = Iso.refl
quoteᶠ-pres-≅ (ν≅μ NFIso.`→ α≅β)   = quoteⁿ-pres-≅ ν≅μ Iso.`→′ quoteᵃ-pres-≅ α≅β
quoteⁿ-pres-≅ (↭.refl ν≋μ)         = =̇.rec (λ {ν} {μ} _ → quoteⁿ ν ≅ quoteⁿ μ) (λ φ≅ψ → quoteᶠ-pres-≅ φ≅ψ Iso.`×′_) Iso.refl ν≋μ
quoteⁿ-pres-≅ (↭.prep φ≅ψ ν≅μ)     = quoteᶠ-pres-≅ φ≅ψ Iso.`×′ quoteⁿ-pres-≅ ν≅μ
quoteⁿ-pres-≅ (↭.swap φ≅ψ ε≅θ ν≅μ) = Iso.trans′ (quoteᶠ-pres-≅ φ≅ψ Iso.`×′ quoteᶠ-pres-≅ ε≅θ Iso.`×′ quoteⁿ-pres-≅ ν≅μ) (Iso.`×-swap _ _ _)
quoteⁿ-pres-≅ (↭.trans ν≅μ μ≅ι)    = Iso.trans′ (quoteⁿ-pres-≅ ν≅μ) (quoteⁿ-pres-≅ μ≅ι)

quote-homo-∪ : (ν μ : NF n) → quoteⁿ (ν NF.∪ μ) ≅ quoteⁿ ν Type.`× quoteⁿ μ
quote-homo-∪ NF.`⊤       μ = Iso.sym (Iso.`×-identityˡ _)
quote-homo-∪ (φ NF.`× ν) μ = Iso.trans′ (Iso.refl Iso.`×′ quote-homo-∪ ν μ) (Iso.sym (Iso.`×-assoc _ _ _))

quote-homo-`→ᶠ : (ν : NF n) (φ : Factor n) → quoteᶠ (ν NF.`→ᶠ φ) ≅ quoteⁿ ν Type.`→ quoteᶠ φ
quote-homo-`→ᶠ ν (μ Factor.`→ α) = Iso.trans′ (quote-homo-∪ ν μ Iso.`→ Iso.refl) (Iso.sym (Iso.`→-curry _ _ _))

quote-homo-`→ⁿ : (ν μ : NF n) → quoteⁿ (ν NF.`→ⁿ μ) ≅ quoteⁿ ν Type.`→ quoteⁿ μ
quote-homo-`→ⁿ ν NF.`⊤       = Iso.sym (Iso.`→-zeroʳ _)
quote-homo-`→ⁿ ν (φ NF.`× μ) = Iso.trans′ (quote-homo-`→ᶠ ν φ Iso.`×′ quote-homo-`→ⁿ ν μ) (Iso.sym (Iso.`→-distribˡ-`× _ _ _))

-- Only up to isomorphism
section : (A : Type n) → quoteⁿ (normalise A) ≅ A
section (Type.var x)  = Iso.trans′ (Iso.`×-identityʳ _) (Iso.`→-identityˡ _)
section Type.`⊤       = Iso.refl
section (A Type.`× B) = Iso.trans′ (quote-homo-∪ (normalise A) (normalise B)) (section A Iso.`×′ section B)
section (A Type.`→ B) = Iso.trans′ (quote-homo-`→ⁿ (normalise A) (normalise B)) (section A Iso.`→′ section B)

-- Up to propositional equality
retractᵃ : (α : Atom n) → normalise (quoteᵃ α) ≡ ↑ α
retractᶠ : (φ : Factor n) → normalise (quoteᶠ φ) ≡ ↑ φ
retractⁿ : (ν : NF n) → normalise (quoteⁿ ν) ≡ ν

retractᵃ (Atom.var x) = ≡.refl

retractᶠ (ν Factor.`→ α) =
  begin
    normalise (quoteⁿ ν) NF.`→ⁿ normalise (quoteᵃ α)
  ≡⟨ ≡.cong₂ NF._`→ⁿ_ (retractⁿ ν) (retractᵃ α) ⟩
    (⌞ ν NF.∪ NF.`⊤ ⌟ NF.`→ α) NF.`× NF.`⊤
  ≡⟨ cong! (NFIso.∪-identityʳ ν) ⟩
    (ν NF.`→ α) NF.`× NF.`⊤
  ∎
  where open ≡.≡-Reasoning

retractⁿ NF.`⊤       = ≡.refl
retractⁿ (φ NF.`× ν) = ≡.cong₂ NF._∪_ (retractᶠ φ) (retractⁿ ν)

normalise-pres-≅⁻ : {A B : Type n} → normalise A ≅ⁿ normalise B → A ≅ B
normalise-pres-≅⁻ {A = A} {B = B} ↓A≅↓B =
  Iso.trans′ (Iso.sym′ (section A)) (_≅_.trans (quoteⁿ-pres-≅ ↓A≅↓B) (section B))

_≟_ : (A B : Type n) → Dec (A ≅ B)
A ≟ B = Dec.map′ normalise-pres-≅⁻ normalise-pres-≅ (normalise A NFIso.≟ⁿ normalise B)

module _ (ext : Extensionality ℓ ℓ) where

  _↔?_ : (A B : Type n) (ρ : Ctx⟦ n ⟧ ℓ) → Maybe (Type⟦ A ⟧ ρ ↔ Type⟦ B ⟧ ρ)
  (A ↔? B) ρ with A ≟ B
  ... | yes A≅B = just (≅⟦ ext ⟧ A≅B ρ)
  ... | no _    = nothing


module _ (ext : Extensionality _ _) {A B : Set} where

  #A #B : Type 2
  #A = Type.var 0F
  #B = Type.var 1F

  ρ : Ctx⟦ 2 ⟧ _
  ρ = (tt , A) , B

  _ : (#A Type.`→ #B Type.`→ #A ≟ #B Type.`→ #A Type.`→ #A) ≡ yes (_≅_.trans
     (_≅_.trans
      (_≅_.trans (_≅_.sym (_≅_.`→-identityˡ (Type.var 0F)))
       (_≅_.trans
        (_≅_.sym (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 0F)))
        (_≅_.sym (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤)))
       _≅_.`→
       _≅_.trans
       (_≅_.trans (_≅_.sym (_≅_.`→-identityˡ (Type.var 1F)))
        (_≅_.trans
         (_≅_.sym (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 1F)))
         (_≅_.sym (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 1F) Type.`⊤)))
        _≅_.`→
        _≅_.trans (_≅_.sym (_≅_.`→-identityˡ (Type.var 0F)))
        (_≅_.trans
         (_≅_.sym (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 0F)))
         (_≅_.sym (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤))))
       (_≅_.trans
        (_≅_.`→-distribˡ-`× ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤)
         (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤)
        (_≅_.trans
         (_≅_.`→-curry ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤)
          Type.`⊤ (Type.var 0F))
         (_≅_.trans
          (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 1F) Type.`⊤ Type.`⊤)
          (_≅_.refl _≅_.`× _≅_.`×-identityˡ Type.`⊤)
          _≅_.`→ _≅_.refl)
         _≅_.`×
         _≅_.`→-zeroʳ ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤))))
      (_≅_.trans
       (_≅_.`→-distribˡ-`× ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)
        ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤ Type.`→ Type.var 0F)
        Type.`⊤)
       (_≅_.trans
        (_≅_.`→-curry ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)
         ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤) (Type.var 0F))
        (_≅_.trans
         (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤
          ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤))
         (_≅_.refl _≅_.`×
          _≅_.`×-identityˡ ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤))
         _≅_.`→ _≅_.refl)
        _≅_.`×
        _≅_.`→-zeroʳ ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤))))
     (_≅_.trans
      ((_≅_.trans
        (_≅_.sym
         (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 0F)
          (Type.`⊤ Type.`→ Type.var 1F) Type.`⊤))
        (_≅_.trans
         (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 0F)
          (Type.`⊤ Type.`→ Type.var 1F)
          _≅_.`× _≅_.refl)
         (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 1F)
          (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤))
        _≅_.`→ _≅_.refl)
       _≅_.`× _≅_.refl)
      (_≅_.trans
       (_≅_.trans
        (_≅_.trans
         (_≅_.trans
          (_≅_.refl _≅_.`×
           _≅_.sym
           (_≅_.`×-identityˡ ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)))
          (_≅_.sym
           (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 1F) Type.`⊤
            ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)))
          _≅_.`→ _≅_.refl)
         (_≅_.sym
          (_≅_.`→-curry ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤)
           ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤) (Type.var 0F)))
         _≅_.`×
         _≅_.sym
         (_≅_.`→-zeroʳ ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤)))
        (_≅_.sym
         (_≅_.`→-distribˡ-`× ((Type.`⊤ Type.`→ Type.var 1F) Type.`× Type.`⊤)
          ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤ Type.`→ Type.var 0F)
          Type.`⊤)))
       (_≅_.trans
        (_≅_.trans (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 1F) Type.`⊤)
         (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 1F)))
        (_≅_.`→-identityˡ (Type.var 1F))
        _≅_.`→
        _≅_.trans
        (_≅_.trans
         (_≅_.trans
          (_≅_.trans (_≅_.refl _≅_.`× _≅_.sym (_≅_.`×-identityˡ Type.`⊤))
           (_≅_.sym
            (_≅_.`×-assoc (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤ Type.`⊤))
           _≅_.`→ _≅_.refl)
          (_≅_.sym
           (_≅_.`→-curry ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)
            Type.`⊤ (Type.var 0F)))
          _≅_.`×
          _≅_.sym
          (_≅_.`→-zeroʳ ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)))
         (_≅_.sym
          (_≅_.`→-distribˡ-`× ((Type.`⊤ Type.`→ Type.var 0F) Type.`× Type.`⊤)
           (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤)))
        (_≅_.trans
         (_≅_.trans (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤)
          (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 0F)))
         (_≅_.`→-identityˡ (Type.var 0F))
         _≅_.`→
         _≅_.trans
         (_≅_.trans (_≅_.`×-comm (Type.`⊤ Type.`→ Type.var 0F) Type.`⊤)
          (_≅_.`×-identityˡ (Type.`⊤ Type.`→ Type.var 0F)))
         (_≅_.`→-identityˡ (Type.var 0F)))))))
  _ = ≡.refl

  _ : _↔?_ ext (#A Type.`→ #B Type.`→ #A) (#B Type.`→ #A Type.`→ #A) ρ ≡
      just (record { to = flip ; from = flip ; to-cong = _ ; from-cong = _ ; inverse = _ })
  _ = ≡.refl
