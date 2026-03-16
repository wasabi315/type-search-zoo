module Rittri89.Normalise where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes)

open import Rittri89.Type as Type using (Type)
open import Rittri89.NF as NF using (Sort; atom; factor; product; NF; Atom; Factor; Product; ⇑_)
import Rittri89.TypeIso as Type
import Rittri89.NFIso as NF

private
  variable
    n : ℕ
    x y : Fin n
    s : Sort
    A B C D : Type n
    α β γ δ : NF n s

infix 4 _≟_

--------------------------------------------------------------------------------

normalise : Type n → Product n
normalise (Type.# x)    = ⇑ NF.# x
normalise Type.unit     = NF.unit
normalise (A Type.* B)  = normalise A NF.* normalise B
normalise (A Type.⇒ B)  = normalise A NF.⇒ normalise B
normalise (Type.list A) = ⇑ NF.list (normalise A)

readback : NF n s → Type n
readback (NF.# x)    = Type.# x
readback (NF.list α) = Type.list (readback α)
readback (α NF.▶ β)  = readback α Type.⇒ readback β
readback NF.unit     = Type.unit
readback (α NF.∷ β)  = readback α Type.* readback β

--------------------------------------------------------------------------------

normalise-preserves-≅ : normalise {n} Preserves Type._≅_ ⟶ NF._≅_
normalise-preserves-≅ Type.refl                     = NF.refl
normalise-preserves-≅ (Type.sym p)                  = NF.sym (normalise-preserves-≅ p)
normalise-preserves-≅ (Type.trans p q)              = NF.trans′ (normalise-preserves-≅ p) (normalise-preserves-≅ q)
normalise-preserves-≅ (p Type.* q)                  = normalise-preserves-≅ p NF.*′ normalise-preserves-≅ q
normalise-preserves-≅ (p Type.⇒ q)                  = normalise-preserves-≅ p NF.⇒′ normalise-preserves-≅ q
normalise-preserves-≅ (Type.list p)                 = NF.⇑′ NF.list′ (normalise-preserves-≅ p)
normalise-preserves-≅ Type.*-identityˡ              = NF.*-identityˡ _
normalise-preserves-≅ (Type.*-comm {A = A} {B = B}) = NF.*-comm (normalise A) (normalise B)
normalise-preserves-≅ (Type.*-assoc {A = A})        = NF.*-assoc (normalise A) _ _
normalise-preserves-≅ Type.⇒-identityˡ              = NF.⇒-identityˡ _
normalise-preserves-≅ Type.uncurry                  = NF.uncurry _ _ _
normalise-preserves-≅ (Type.⇒-zeroʳ {A = A})        = NF.⇒-zeroʳ (normalise A)
normalise-preserves-≅ (Type.distrib {B = B})        = NF.distrib _ (normalise B) _

readback-preserves-≅ : readback {n} {s} Preserves NF._≅_ ⟶ Type._≅_
readback-preserves-≅ NF.refl         = Type.refl
readback-preserves-≅ (NF.trans p q)  = Type.trans′ (readback-preserves-≅ p) (readback-preserves-≅ q)
readback-preserves-≅ (NF.list p)     = Type.list (readback-preserves-≅ p)
readback-preserves-≅ (p NF.▶ q)      = readback-preserves-≅ p Type.⇒′ readback-preserves-≅ q
readback-preserves-≅ (p NF.∷ q)      = readback-preserves-≅ p Type.*′ readback-preserves-≅ q
readback-preserves-≅ (NF.swap p q r) = Type.*-swap (readback-preserves-≅ p) (readback-preserves-≅ q) (readback-preserves-≅ r)

readback-homo-* : (α β : Product n) → readback α Type.* readback β Type.≅ readback (α NF.* β)
readback-homo-* NF.unit     β = Type.*-identityˡ
readback-homo-* (α NF.∷ α′) β = Type.trans′ Type.*-assoc (Type.refl Type.*′ readback-homo-* α′ β)

readback-homo-⇒ : (α : Product n) (β : NF n s) → readback α Type.⇒ readback β Type.≅ readback (α NF.⇒ β)
readback-homo-⇒ α (NF.# x)    = Type.refl
readback-homo-⇒ α (NF.list β) = Type.refl
readback-homo-⇒ α (β NF.▶ β′) = Type.trans′ Type.uncurry (readback-homo-* α β Type.⇒′ Type.refl)
readback-homo-⇒ α NF.unit     = Type.⇒-zeroʳ
readback-homo-⇒ α (β NF.∷ β′) = Type.trans′ Type.distrib (readback-homo-⇒ α β Type.*′ readback-homo-⇒ α β′)

section : (A : Type n) → A Type.≅ readback (normalise A)
section (Type.# x)    = Type.trans′ Type.⇒-identityˡ (Type.sym′ Type.*-identityʳ)
section Type.unit     = Type.refl
section (A Type.* B)  = Type.trans′ (section A Type.*′ section B) (readback-homo-* (normalise A) (normalise B))
section (A Type.⇒ B)  = Type.trans′ (section A Type.⇒′ section B) (readback-homo-⇒ (normalise A) (normalise B))
section (Type.list A) = Type.trans′ (Type.list′ (section A)) (Type.trans′ Type.⇒-identityˡ (Type.sym′ Type.*-identityʳ))

retract : (α : NF n s) → normalise (readback α) ≡ ⇑ α
retract (NF.# x)    = ≡.refl
retract (NF.list α) = ≡.cong (λ β → ⇑ NF.list β) (retract α)
retract (α NF.▶ β)  = ≡.trans (≡.cong₂ NF._⇒_ (retract α) (retract β)) (≡.cong (λ α → ⇑ (α NF.▶ β)) (NF.*-strictIdentityʳ α))
retract NF.unit     = ≡.refl
retract (α NF.∷ β)  = ≡.cong₂ NF._*_ (retract α) (retract β)

normalise-preserves-≅⁻ : normalise A NF.≅ normalise B → A Type.≅ B
normalise-preserves-≅⁻ p = Type.trans′ (section _) (Type.trans′ (readback-preserves-≅ p) (Type.sym′ (section _)))

_≟_ : (A B : Type n) → Dec (A Type.≅ B)
A ≟ B = Dec.map′ normalise-preserves-≅⁻ normalise-preserves-≅ (normalise A NF.≟ normalise B)

module _ where
  open import Data.Fin.Patterns using (0F; 1F)

  open import Rittri89.Type
  open import Rittri89.TypeIso

  pattern X = # 1F
  pattern Y = # 0F
  pattern foo = trans distrib (trans uncurry (trans *-assoc (refl * *-identityˡ) ⇒ refl) * ⇒-zeroʳ)
  pattern swp = trans (sym *-assoc) (trans (*-comm * refl) *-assoc)
  pattern idr = trans *-comm *-identityˡ

  itlist-sig fold_left-sig : Type 2
  itlist-sig    = (X ⇒ Y ⇒ Y) ⇒ list X ⇒ Y ⇒ Y
  fold_left-sig = (X * Y ⇒ Y) ⇒ Y ⇒ list X ⇒ Y

  _ : (itlist-sig ≟ fold_left-sig) ≡ yes (trans
     (trans
      (trans
       (trans ⇒-identityˡ (sym idr) ⇒
        trans (trans ⇒-identityˡ (sym idr) ⇒ trans ⇒-identityˡ (sym idr))
        foo)
       foo
       ⇒
       trans
       (trans (list (trans ⇒-identityˡ (sym idr)))
        (trans ⇒-identityˡ (sym idr))
        ⇒
        trans (trans ⇒-identityˡ (sym idr) ⇒ trans ⇒-identityˡ (sym idr))
        foo)
       foo)
      foo)
     (trans ((refl * swp ⇒ refl) * refl)
      (sym
       (trans
        (trans
         (trans (trans ⇒-identityˡ (sym idr) * trans ⇒-identityˡ (sym idr))
          (trans *-assoc (refl * *-identityˡ))
          ⇒ trans ⇒-identityˡ (sym idr))
         (trans distrib
          (trans uncurry
           (trans *-assoc (refl * trans *-assoc (refl * *-identityˡ)) ⇒ refl)
           * ⇒-zeroʳ))
         ⇒
         trans
         (trans ⇒-identityˡ (sym idr) ⇒
          trans
          (trans (list (trans ⇒-identityˡ (sym idr)))
           (trans ⇒-identityˡ (sym idr))
           ⇒ trans ⇒-identityˡ (sym idr))
          foo)
         foo)
        foo))))
  _ = ≡.refl
