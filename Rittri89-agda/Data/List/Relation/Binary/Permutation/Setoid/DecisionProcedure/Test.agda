module Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure.Test where

open import Data.Nat.Properties using (≡-decSetoid)
open import Relation.Binary.Bundles using (DecSetoid)
open import Data.List.Base using (List; _∷_; [])
import Data.List.Relation.Binary.Permutation.Homogeneous as ↭
open import Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure ≡-decSetoid
  using (permutation?)
import Data.List.Relation.Binary.Equality.Setoid (DecSetoid.setoid ≡-decSetoid) as ≋
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; no)

_ : permutation? (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ []) ≡ yes
  (↭.trans
    (↭.prep ≡.refl
      (↭.trans
      (↭.prep ≡.refl
        (↭.trans (↭.prep ≡.refl (↭.refl ≋.[]))
        (↭.prep ≡.refl (↭.refl ≋.[]))))
      (↭.trans
        (↭.trans (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
        (↭.swap ≡.refl ≡.refl (↭.refl ≋.[])))
        (↭.prep ≡.refl (↭.prep ≡.refl (↭.refl ≋.[]))))))
    (↭.trans
      (↭.trans (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
      (↭.swap ≡.refl ≡.refl (↭.refl (≡.refl ≋.∷ ≋.[]))))
      (↭.prep ≡.refl
      (↭.trans
        (↭.trans (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
        (↭.swap ≡.refl ≡.refl (↭.refl ≋.[])))
        (↭.prep ≡.refl (↭.prep ≡.refl (↭.refl ≋.[])))))))
_ = ≡.refl

_ : permutation? (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (3 ∷ 2 ∷ 5 ∷ 1 ∷ 4 ∷ []) ≡ yes
  (↭.trans
    (↭.prep ≡.refl
      (↭.trans
      (↭.prep ≡.refl
        (↭.trans
        (↭.prep ≡.refl
          (↭.trans
          (↭.prep ≡.refl
            (↭.trans (↭.prep ≡.refl (↭.refl ≋.[]))
            (↭.prep ≡.refl (↭.refl ≋.[]))))
          (↭.trans
            (↭.trans (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
            (↭.swap ≡.refl ≡.refl (↭.refl ≋.[])))
            (↭.prep ≡.refl (↭.prep ≡.refl (↭.refl ≋.[]))))))
        (↭.prep ≡.refl (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[])))))
      (↭.trans
        (↭.trans
        (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
        (↭.swap ≡.refl ≡.refl (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))))
        (↭.prep ≡.refl
        (↭.prep ≡.refl (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[])))))))
    (↭.trans
      (↭.trans
      (↭.refl
        (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
      (↭.swap ≡.refl ≡.refl
        (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))))
      (↭.prep ≡.refl
      (↭.trans
        (↭.trans
        (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
        (↭.swap ≡.refl ≡.refl (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))))
        (↭.prep ≡.refl
        (↭.trans
          (↭.trans (↭.refl (≡.refl ≋.∷ ≡.refl ≋.∷ ≡.refl ≋.∷ ≋.[]))
          (↭.swap ≡.refl ≡.refl (↭.refl (≡.refl ≋.∷ ≋.[]))))
          (↭.prep ≡.refl (↭.prep ≡.refl (↭.refl (≡.refl ≋.∷ ≋.[]))))))))))
_ = ≡.refl

_ : permutation? (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ 1 ∷ []) ≡ no _
_ = ≡.refl
