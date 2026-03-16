module Rittri89.NFIso where

open import Data.Bool.Base using (false; true)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as Fin
open import Data.Nat.Base using (ℕ; suc; zero; 2+)
open import Data.Nat.Properties as ℕ using (suc-injective)
open import Data.Product.Base as × using (∃-syntax; ∃₂; _×_; _,_)
open import Function.Base using (_∘_)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contraposition)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes; no; _because_; _×-dec_)
open import Relation.Nullary.Reflects using (invert)

open import Rittri89.NF

private
  variable
    n : ℕ
    x y : Fin n
    s : Sort
    α β γ δ α′ β′ γ′ : NF n s

infix  4 _≅_ _≟_ _≋_
infixr 5 _▶_ _▶′_
infixr 6 _∷_ _∷′_

--------------------------------------------------------------------------------

data _≅_ {n} : NF n s → NF n s → Set where
  -- Equivalence
  refl  : α ≅ α
  trans : {α β γ : Product n} → (p : α ≅ β) (q : β ≅ γ) → α ≅ γ

  -- Congruence
  list : (p : α ≅ β) → list α ≅ list β
  _▶_  : (p : α ≅ β) (q : γ ≅ δ) → α ▶ γ ≅ β ▶ δ
  _∷_  : (p : α ≅ β) (q : γ ≅ δ) → α ∷ γ ≅ β ∷ δ

  -- Permutation
  swap : (p : α ≅ α′) (q : β ≅ β′) (r : γ ≅ γ′) → α ∷ β ∷ γ ≅ β′ ∷ α′ ∷ γ′

pattern _▶- {n} {s} {α} {β} {γ} p = _▶_ {n} {s} {α} {β} p (refl {α = γ})
pattern -▶_ {n} {s} {α} {β} {γ} p = _▶_ {n} {s} {γ = β} {δ = γ} (refl {α = α}) p
pattern _∷- {n} {s} {α} {β} {γ} p = _∷_ {n} {s} {α} {β} p (refl {α = γ})
pattern -∷_ {n} {s} {α} {β} {γ} p = _∷_ {n} {s} {γ = β} {δ = γ} (refl {α = α}) p

sym : α ≅ β → β ≅ α
sym refl         = refl
sym (trans p q)  = trans (sym q) (sym p)
sym (list p)     = list (sym p)
sym (p ▶ q)      = sym p ▶ sym q
sym (p ∷ q)      = sym p ∷ sym q
sym (swap p q r) = swap (sym q) (sym p) (sym r)

trans′ : {α β γ : NF n s} → α ≅ β → β ≅ γ → α ≅ γ
trans′ refl     q         = q
trans′ p        refl      = p
trans′ (list p) (list q)  = list (trans′ p q)
trans′ (p ▶ q)  (p′ ▶ q′) = trans′ p p′ ▶ trans′ q q′
trans′ {s = product} p q  = trans p q

_▶′_ : α ≅ β → γ ≅ δ → α ▶ γ ≅ β ▶ δ
refl ▶′ refl = refl
p    ▶′ q    = p ▶ q

_∷′_ : α ≅ β → γ ≅ δ → α ∷ γ ≅ β ∷ δ
refl ∷′ refl = refl
p    ∷′ q    = p ∷ q

#′_ : x ≡ y → # x ≅ # y
#′ ≡.refl = refl

list′ : α ≅ β → list α ≅ list β
list′ refl = refl
list′ p    = list p

↑′_ : α ≅ β → ↑ α ≅ ↑ β
↑′ p = refl ▶′ p

⇑′_ : ∀ {s} {α β : NF n s} → α ≅ β → ⇑ α ≅ ⇑ β
⇑′_ {s = atom}    p = (refl ▶′ p) ∷′ refl
⇑′_ {s = factor}  p = p ∷′ refl
⇑′_ {s = product} p = p

--------------------------------------------------------------------------------

_*- : {α β γ : Product n} → α ≅ β → α * γ ≅ β * γ
refl       *- = refl
trans p q  *- = trans′ (p *-) (q *-)
(p ∷ q)    *- = p ∷ (q *-)
swap p q r *- = swap p q (r *-)

-*_ : {α β γ : Product n} → β ≅ γ → α * β ≅ α * γ
-*_ {α = unit}  p = p
-*_ {α = α ∷ β} p = refl ∷′ (-* p)

_*′_ : {α β : NF n s} {γ δ : Product n} → α ≅ β → γ ≅ δ → α * γ ≅ β * δ
_*′_ {s = atom}    p q = (↑′ p) ∷′ q
_*′_ {s = factor}  p q = p ∷′ q
_*′_ {s = product} p q = trans′ (p *-) (-* q)

_⇒- : {α β : Product n} {γ : NF n s} → α ≅ β → α ⇒ γ ≅ β ⇒ γ
_⇒- {s = atom} p = p ▶′ refl
_⇒- {s = factor} {γ = _ ▶ _} p = (p *′ refl) ▶′ refl
_⇒- {s = product} {γ = unit}  p = refl
_⇒- {s = product} {γ = _ ∷ _} p = (p ⇒-) ∷′ (p ⇒-)

-⇒_ : {α : Product n} {β γ : NF n s} → β ≅ γ → α ⇒ β ≅ α ⇒ γ
-⇒ refl       = refl
-⇒ trans p q  = trans′ (-⇒ p) (-⇒ q)
-⇒ list p     = refl ▶′ list p
-⇒ (p ▶ q)    = (refl *′ p) ▶′ q
-⇒ (p ∷ q)    = (-⇒ p) ∷′ (-⇒ q)
-⇒ swap p q r = swap (-⇒ p) (-⇒ q) (-⇒ r)

_⇒′_ : {α β : Product n} {γ δ : NF n s} → α ≅ β → γ ≅ δ → α ⇒ γ ≅ β ⇒ δ
_⇒′_ {s = atom} p q = p ▶′ q
_⇒′_ {s = factor} {γ = _ ▶ _} {δ = _ ▶ _} p refl    = (p *-) ▶′ refl
_⇒′_ {s = factor} {γ = _ ▶ _} {δ = _ ▶ _} p (q ▶ r) = (p *′ q) ▶′ r
_⇒′_ {s = product} p q = trans′ (p ⇒-) (-⇒ q)

¬unit≅cons : ¬ unit ≅ α ∷ β
¬unit≅cons (trans {β = unit}  p q) = ¬unit≅cons q
¬unit≅cons (trans {β = α ∷ β} p q) = ¬unit≅cons p

*-strictIdentityˡ : (α : Product n) → unit * α ≡ α
*-strictIdentityˡ _ = ≡.refl

*-identityˡ : (α : Product n) → unit * α ≅ α
*-identityˡ _ = refl

*-strictIdentityʳ : (α : Product n) → α * unit ≡ α
*-strictIdentityʳ unit     = ≡.refl
*-strictIdentityʳ (α ∷ α′) = ≡.cong (α ∷_) (*-strictIdentityʳ α′)

*-identityʳ : (α : Product n) → α * unit ≅ α
*-identityʳ unit     = refl
*-identityʳ (α ∷ α′) = refl ∷′ *-identityʳ α′

shift : α ≅ β → (γ δ : Product n) → α ∷ γ * δ ≅ γ * β ∷ δ
shift p unit     δ = p ∷′ refl
shift p (γ ∷ γs) δ = trans′ (swap p refl refl) (refl ∷′ shift refl γs δ)

*-comm : (α β : Product n) → α * β ≅ β * α
*-comm unit     β = sym (*-identityʳ β)
*-comm (α ∷ α′) β = trans′ (refl ∷′ *-comm α′ β) (shift refl β α′)

*-strictAssoc : (α β γ : Product n) → (α * β) * γ ≡ α * (β * γ)
*-strictAssoc unit     β γ = ≡.refl
*-strictAssoc (α ∷ α′) β γ = ≡.cong (α ∷_) (*-strictAssoc α′ β γ)

*-assoc : (α β γ : Product n) → (α * β) * γ ≅ α * (β * γ)
*-assoc unit     β γ = refl
*-assoc (α ∷ α′) β γ = refl ∷′ *-assoc α′ β γ

⇒-identityˡ : (α : Product n) → α ≅ unit ⇒ α
⇒-identityˡ unit          = refl
⇒-identityˡ ((_ ▶ _) ∷ α) = refl ∷′ ⇒-identityˡ α

uncurry : (α β γ : Product n) → α ⇒ (β ⇒ γ) ≅ (α * β) ⇒ γ
uncurry α β unit           = refl
uncurry α β ((γ ▶ γ′) ∷ δ) = trans′ ((sym (*-assoc α β γ) ▶′ refl) ∷′ refl) (refl ∷′ uncurry α β δ)

⇒-zeroʳ : (α : Product n) → α ⇒ unit ≅ unit
⇒-zeroʳ _ = refl

distrib : (α β γ : Product n) → α ⇒ (β * γ) ≅ (α ⇒ β) * (α ⇒ γ)
distrib α unit     γ = refl
distrib α (β ∷ β′) γ = refl ∷′ distrib α β′ γ

--------------------------------------------------------------------------------

#-injective : # x ≅ # y → x ≡ y
#-injective refl = ≡.refl

list-injective : list α ≅ list β → α ≅ β
list-injective refl     = refl
list-injective (list p) = p

▶-injective : (α ▶ γ) ≅ (β ▶ δ) → (α ≅ β) × (γ ≅ δ)
▶-injective refl    = refl , refl
▶-injective (p ▶ q) = p , q

α≅β⇒|α|≡|β| : α ≅ β → length α ≡ length β
α≅β⇒|α|≡|β| refl         = ≡.refl
α≅β⇒|α|≡|β| (trans p q)  = ≡.trans (α≅β⇒|α|≡|β| p) (α≅β⇒|α|≡|β| q)
α≅β⇒|α|≡|β| (p ∷ q)      = ≡.cong suc (α≅β⇒|α|≡|β| q)
α≅β⇒|α|≡|β| (swap p q r) = ≡.cong 2+ (α≅β⇒|α|≡|β| r)

data _≋_ {n} : Product n → Product n → Set where
  unit : unit ≋ unit
  _∷_  : (p : α ≅ β) (q : γ ≋ δ) → α ∷ γ ≋ β ∷ δ

≋-refl : α ≋ α
≋-refl {α = unit}  = unit
≋-refl {α = α ∷ β} = refl ∷ ≋-refl

≋⇒≅ : α ≋ β → α ≅ β
≋⇒≅ unit    = refl
≋⇒≅ (p ∷ q) = p ∷′ ≋⇒≅ q

trans-≋ˡ : α ≋ β → β ≅ γ → α ≅ γ
trans-≋ˡ p           refl         = ≋⇒≅ p
trans-≋ˡ p           (trans q r)  = trans′ (trans-≋ˡ p q) r
trans-≋ˡ (p ∷ q)     (r ∷ s)      = trans′ p r ∷′ trans-≋ˡ q s
trans-≋ˡ (p ∷ q ∷ r) (swap s t u) = swap (trans′ p s) (trans′ q t) (trans-≋ˡ r u)

trans-≋ʳ : α ≅ β → β ≋ γ → α ≅ γ
trans-≋ʳ refl         q           = ≋⇒≅ q
trans-≋ʳ (trans p q)  r           = trans′ p (trans-≋ʳ q r)
trans-≋ʳ (p ∷ q)      (r ∷ s)     = trans′ p r ∷′ trans-≋ʳ q s
trans-≋ʳ (swap p q r) (s ∷ t ∷ u) = swap (trans′ p t) (trans′ q s) (trans-≋ʳ r u)

split : ∀ (α : Factor n) (αs βs : Product n) {γs}
  → γs ≅ (αs * α ∷ βs)
  → ∃₂ λ (xs : Product _) ys → γs ≋ (xs * α ∷ ys) × (xs * ys) ≅ (αs * βs)
split α αs βs p = helper αs βs p ≋-refl
  where
    helper : ∀ (αs βs : Product _) {γs δs}
      → γs ≅ δs
      → δs ≋ αs * α ∷ βs
      → ∃₂ λ (xs : Product _) ys → γs ≋ (xs * α ∷ ys) × (xs * ys) ≅ (αs * βs)
    helper unit βs refl (p ∷ s) = unit , _ , p ∷ ≋-refl , ≋⇒≅ s
    helper (α ∷ αs) βs refl s = _ ∷ αs , βs , s , refl
    helper αs βs (trans p q) s
      using xs  , ys  , eq  , h  ← helper αs βs q s
      using xs′ , ys′ , eq′ , h′ ← helper xs ys p eq
      = xs′ , ys′ , eq′ , trans′ h′ h
    helper unit βs (p ∷ q) (r ∷ s) = unit , _ , trans′ p r ∷ ≋-refl , trans-≋ʳ q s
    helper (α ∷ αs) βs (p ∷ q) (r ∷ s)
      using xs , ys , eq , h ← helper αs βs q s
      = α ∷ xs , ys , trans′ p r ∷ eq , refl ∷′ h
    helper unit unit (swap _ _ _) (_ ∷ ())
    helper unit (β ∷ _) (swap p q r) (s ∷ t ∷ u) =
      β ∷ unit , _ , trans′ p t ∷ trans′ q s ∷ ≋-refl , refl ∷′ trans-≋ʳ r u
    helper (α ∷ unit) βs (swap p q r) (s ∷ t ∷ u) =
      unit , α ∷ _ , trans′ p t ∷ trans′ q s ∷ ≋-refl , refl ∷′ trans-≋ʳ r u
    helper (α ∷ α′ ∷ αs) βs (swap p q r) (s ∷ t ∷ u)
      using xs , ys , eq , h ← helper αs βs r u
      = α′ ∷ α ∷ xs , ys , trans′ p t ∷ trans′ q s ∷ eq , swap refl refl h

differentHead : {α β : Factor n} {αs βs : Product n}
  → ¬ α ≅ β
  → α ∷ αs ≅ β ∷ βs
  → ∃[ γs ] (αs ≅ β ∷ γs) × (α ∷ γs ≅ βs)
differentHead {α = α} {β} {αs} {βs} neq p with split β unit βs p
... | unit   , _  , q ∷ _ , _ = contradiction q neq
... | x ∷ xs , ys , q ∷ r , s =
      xs * ys , trans-≋ˡ r (sym (shift refl xs ys)) , trans′ (q ∷′ refl) s

dropMiddleElement-≋ : ∀ {α : Factor n} (αs βs : Product n) {γs δs}
  → αs * α ∷ γs ≋ βs * α ∷ δs
  → αs * γs ≅ βs * δs
dropMiddleElement-≋ unit     unit     (_ ∷ p) = ≋⇒≅ p
dropMiddleElement-≋ unit     (β ∷ βs) (p ∷ q) = trans-≋ˡ q (sym (shift (sym p) βs _))
dropMiddleElement-≋ (α ∷ αs) unit     (p ∷ q) = trans-≋ʳ (shift p αs _) q
dropMiddleElement-≋ (α ∷ αs) (β ∷ βs) (p ∷ q) = p ∷′ dropMiddleElement-≋ αs βs q

dropMiddleElement : ∀ {α : Factor n} (αs βs : Product n) {γs δs}
  → αs * α ∷ γs ≅ βs * α ∷ δs
  → αs * γs ≅ βs * δs
dropMiddleElement {α = α} αs βs {γs} {δs} p
  using xs , ys , eq , h ← split α βs δs p
  = trans′ (dropMiddleElement-≋ {α = α} αs xs eq) h

drop-∷ : {α : Factor n} {αs βs : Product n} → α ∷ αs ≅ α ∷ βs → αs ≅ βs
drop-∷ = dropMiddleElement unit unit

_≟_ : (α β : NF n s) → Dec (α ≅ β)
# x    ≟ # y    = Dec.map′ #′_ #-injective (x Fin.≟ y)
# x    ≟ list α = no λ ()
list α ≟ # y    = no λ ()
list α ≟ list β = Dec.map′ list′ list-injective (α ≟ β)
α ▶ α′ ≟ β ▶ β′ = Dec.map′ (λ (p , q) → p ▶′ q) ▶-injective (α ≟ β ×-dec α′ ≟ β′)
_≟_ {s = product} α β with length α ℕ.≟ length β
... | false because neq = no (contraposition α≅β⇒|α|≡|β| (invert neq))
... | true  because eq  = worker α β (invert eq)
  where
    find : (α : Factor n) (β : Product n) → Dec (∃[ γ ] α ∷ γ ≅ β)
    find α unit     = no λ (_ , h) → contradiction (sym h) ¬unit≅cons
    find α (β ∷ βs) with α ≟ β
    ... | true  because p = yes (βs , invert p ∷′ refl)
    ... | false because p = Dec.map′ fwd bwd (find α βs)
      where
        fwd : ∃[ γs ] α ∷ γs ≅ βs → ∃[ γs ] α ∷ γs ≅ β ∷ βs
        fwd (γs , p) = β ∷ γs , trans′ (swap refl refl refl) (refl ∷′ p)

        bwd : ∃[ γs ] α ∷ γs ≅ β ∷ βs → ∃[ γs ] α ∷ γs ≅ βs
        bwd (γs , q) using δs , _ , r ← differentHead (invert p) q = δs , r

    worker : (α β : Product n) → length α ≡ length β → Dec (α ≅ β)
    worker unit     unit _  = yes refl
    worker (α ∷ αs) βs   eq with find α βs
    ... | false because p = no (contraposition (_ ,_) (invert p))
    ... | yes (γs , p) = Dec.map′ fwd bwd (worker αs γs eq′)
      where
        fwd : αs ≅ γs → α ∷ αs ≅ βs
        fwd q = trans′ (refl ∷′ q) p

        bwd : α ∷ αs ≅ βs → αs ≅ γs
        bwd q = drop-∷ (trans′ q (sym p))

        eq′ : length αs ≡ length γs
        eq′ = suc-injective (≡.trans eq (≡.sym (α≅β⇒|α|≡|β| p)))

--------------------------------------------------------------------------------

isEquivalence : ∀ n s → IsEquivalence (_≅_ {n} {s})
isEquivalence n s = record { refl = refl ; sym = sym ; trans = trans′ }

isDecEquivalence : ∀ n s → IsDecEquivalence (_≅_ {n} {s})
isDecEquivalence n s = record { isEquivalence = isEquivalence n s ; _≟_ = _≟_ }

setoid : ℕ → Sort → Setoid _ _
setoid n s = record { isEquivalence = isEquivalence n s }

decSetoid : ℕ → Sort → DecSetoid _ _
decSetoid n s = record { isDecEquivalence = isDecEquivalence n s }
