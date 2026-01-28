open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Permutation.Setoid.DecisionProcedure
  {a ℓ} (S : DecSetoid a ℓ) where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Binary.Permutation.Setoid (DecSetoid.setoid S)
  using (_↭_; refl; prep; swap; trans; ↭-refl; ↭-sym; ↭-trans′; ↭-transˡ-≋; ↭-swap)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties (DecSetoid.setoid S)
  using (¬x∷xs↭[]; ↭-shift; ↭-split; drop-∷; xs↭ys⇒|xs|≡|ys|)
open import Data.List.Relation.Binary.Equality.Setoid (DecSetoid.setoid S) as ≋
  using (_∷_)
open import Data.Nat.Properties as ℕ using (suc-injective)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes; no; _because_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contraposition)

open module ≈ = DecSetoid S using (_≈_; _≟_)

--------------------------------------------------------------------------------

prep′ : ∀ {x y xs ys} → x ≈ y → xs ↭ ys → x ∷ xs ↭ y ∷ ys
prep′ x≈y (refl xs≈ys)       = refl (x≈y ∷ xs≈ys)
prep′ x≈y xs↭ys@(prep _ _)   = prep x≈y xs↭ys
prep′ x≈y xs↭ys@(swap _ _ _) = prep x≈y xs↭ys
prep′ x≈y xs↭ys@(trans _ _)  = prep x≈y xs↭ys

↭-prep′ : ∀ x {xs ys} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep′ _ = prep′ ≈.refl

differentHead : ∀ {x y xs ys}
  → ¬ x ≈ y
  → x ∷ xs ↭ y ∷ ys
  → ∃[ zs ] (xs ↭ y ∷ zs) × (x ∷ zs ↭ ys)
differentHead {x} {y} {xs} {ys} x≉y x∷xs↭y∷ys with ↭-split y [] ys x∷xs↭y∷ys
... | [] , ws , x≈y ∷ xs≋ws , ws↭ys = contradiction x≈y x≉y
... | z ∷ zs , ws , x≈z ∷ xs≋zs++y∷ws , z∷zs++ws↭ys =
        zs ++ ws ,
        ↭-transˡ-≋ xs≋zs++y∷ws (↭-shift zs ws) ,
        ↭-trans′ (prep′ x≈z ↭-refl) z∷zs++ws↭ys

find : ∀ x xs → Dec (∃[ ys ] x ∷ ys ↭ xs)
find x [] = no λ (ys , x∷ys↭[]) → ¬x∷xs↭[] x∷ys↭[]
find x (y ∷ xs) with x ≟ y
... | true  because [x≈y] = yes (xs , prep′ (invert [x≈y]) ↭-refl)
... | false because [x≉y] = Dec.map′ fwd bwd (find x xs)
  where
    fwd : ∃[ ys ] x ∷ ys ↭ xs → ∃[ ys ] x ∷ ys ↭ y ∷ xs
    fwd (ys , x∷ys↭xs) = y ∷ ys , ↭-trans′ (↭-swap x y ↭-refl) (↭-prep′ y x∷ys↭xs)

    bwd : ∃[ ys ] x ∷ ys ↭ y ∷ xs → ∃[ ys ] x ∷ ys ↭ xs
    bwd (ys , x∷ys↭y∷xs)
      using zs , _ , x∷zs↭xs ← differentHead (invert [x≉y]) x∷ys↭y∷xs
      = zs , x∷zs↭xs

permutation? : ∀ xs ys → Dec (xs ↭ ys)
permutation? xs ys with length xs ℕ.≟ length ys
... | false because [|xs|≢|ys|] = no (contraposition xs↭ys⇒|xs|≡|ys| (invert [|xs|≢|ys|]))
... | true  because [|xs|≡|ys|] = worker xs ys (invert [|xs|≡|ys|])
  where
    worker : ∀ xs ys → length xs ≡ length ys → Dec (xs ↭ ys)
    worker []       [] _            = yes ↭-refl
    worker (x ∷ xs) ys suc|xs|≡|ys| with find x ys
    ... | false because ∄x∷zs↭ys = no (contraposition (_ ,_) (invert ∄x∷zs↭ys))
    ... | yes (zs , x∷zs↭ys) = Dec.map′ fwd bwd (worker xs zs |xs|≡|zs|)
      where
        fwd : xs ↭ zs → x ∷ xs ↭ ys
        fwd xs↭zs = ↭-trans′ (↭-prep′ x xs↭zs) x∷zs↭ys

        bwd : x ∷ xs ↭ ys → xs ↭ zs
        bwd x∷xs↭ys = drop-∷ (↭-trans′ x∷xs↭ys (↭-sym x∷zs↭ys))

        |xs|≡|zs| : length xs ≡ length zs
        |xs|≡|zs| = suc-injective (≡.trans suc|xs|≡|ys| (≡.sym (xs↭ys⇒|xs|≡|ys| x∷zs↭ys)))
