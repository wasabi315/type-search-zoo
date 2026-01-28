module Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure.Test where

open import Data.Nat.Properties using (≡-decSetoid)
open import Relation.Binary.Bundles using (DecSetoid)
open import Data.List.Base using (_∷_; [])
import Data.List.Relation.Binary.Permutation.Homogeneous as ↭
open import Data.List.Relation.Binary.Permutation.Setoid (DecSetoid.setoid ≡-decSetoid)
  using (↭-prep; ↭-swap; ↭-reflexive; ↭-trans; ↭-refl)
open import Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure ≡-decSetoid
  using (permutation?)
import Data.List.Relation.Binary.Equality.Setoid (DecSetoid.setoid ≡-decSetoid) as ≋
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (yes; no)

_ : permutation? (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ []) ≡ yes
  (↭-trans
    (↭-prep 1 (↭-swap 2 3 ↭-refl))
    (↭-trans
      (↭-swap 1 3 ↭-refl)
      (↭-prep 3 (↭-swap 1 2 ↭-refl))))
_ = refl

_ : permutation? (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (3 ∷ 2 ∷ 5 ∷ 1 ∷ 4 ∷ []) ≡ yes
  (↭-trans
    (↭-prep 1
      (↭-trans
        (↭-prep 2 (↭-prep 3 (↭-swap 4 5 ↭-refl)))
        (↭-swap 2 3 ↭-refl)))
      (↭-trans
        (↭-swap 1 3 ↭-refl)
        (↭-prep 3
          (↭-trans
            (↭-swap 1 2 ↭-refl)
            (↭-prep 2 (↭-swap 1 5 ↭-refl))))))
_ = refl

_ : permutation? (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ 1 ∷ []) ≡ no _
_ = refl
