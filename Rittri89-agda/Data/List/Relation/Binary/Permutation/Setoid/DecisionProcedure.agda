open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure
  {a ℓ} (S : DecSetoid a ℓ) where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Permutation.Setoid (DecSetoid.setoid S)
  using (_↭_; ↭-refl; ↭-sym; ↭-trans′; ↭-reflexive-≋; ↭-prep)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties (DecSetoid.setoid S)
  using (¬x∷xs↭[]; ↭-shift; ↭-split; drop-∷)
open import Data.List.Relation.Binary.Equality.Setoid (DecSetoid.setoid S) as ≋
  using (_≋_; []; _∷_; ≋-refl; ≋-sym)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes; no; _because_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contraposition)

open module ≈ = DecSetoid S using (_≈_; _≟_) renaming (Carrier to A)

--------------------------------------------------------------------------------

¬xs++x∷ys≋[] : ∀ xs x ys → ¬ xs ++ x ∷ ys ≋ []
¬xs++x∷ys≋[] []       x ys ()
¬xs++x∷ys≋[] (y ∷ xs) x ys ()

find : ∀ x xs → Dec (∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ xs)
find x [] = no λ (ls , rs , eq) → ¬xs++x∷ys≋[] ls x rs eq
find x (y ∷ xs) with x ≟ y
... | true  because [x≈y] = yes ([] , xs , invert [x≈y] ∷ ≋-refl)
... | false because [x≉y] = Dec.map′ fwd bwd (find x xs)
  where
    fwd : ∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ xs →
          ∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ y ∷ xs
    fwd (ls , rs , p) = y ∷ ls , rs , ≈.refl ∷ p

    bwd : ∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ y ∷ xs →
          ∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ xs
    bwd ([]     , rs , x≈y ∷ p) = contradiction x≈y (invert [x≉y])
    bwd (z ∷ ls , rs , z≈y ∷ p) = ls , rs , p

permutation? : ∀ xs ys → Dec (xs ↭ ys)
permutation? [] [] = yes ↭-refl
permutation? [] (x ∷ ys) = no λ p → ¬x∷xs↭[] (↭-sym p)
permutation? (x ∷ xs) ys with find x ys
... | false because ∄ls++x∷rs≋ys = no (contraposition split (invert ∄ls++x∷rs≋ys))
  where
    split : x ∷ xs ↭ ys → ∃[ ls ] ∃[ rs ] ls ++ x ∷ rs ≋ ys
    split x∷xs↭ys
      using ls , rs , eq , _ ← ↭-split x [] xs (↭-sym x∷xs↭ys)
      = ls , rs , ≋-sym eq
... | yes (ls , rs , ls++x∷rs≋ys) = Dec.map′ fwd bwd (permutation? xs (ls ++ rs))
  where
    fwd : xs ↭ ls ++ rs → x ∷ xs ↭ ys
    fwd xs↭ls++rs =
      ↭-trans′ (↭-prep x xs↭ls++rs)
      (↭-trans′ (↭-sym (↭-shift ls rs))
      (↭-reflexive-≋ ls++x∷rs≋ys))

    bwd : x ∷ xs ↭ ys → xs ↭ ls ++ rs
    bwd x∷xs↭ys = drop-∷ (↭-trans′ x∷xs↭ys
                         (↭-trans′ (↭-reflexive-≋ (≋-sym ls++x∷rs≋ys))
                         (↭-shift ls rs)))
