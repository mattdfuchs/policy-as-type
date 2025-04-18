open import Agda.Primitive using (Level; lzero)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; _≡_)
open import Relation.Nullary using (Dec)
open import Data.List.Membership.DecSetoid using (_∈?_)
open import Data.List.Membership.Setoid using (_∈_)

-- Step 1: Manually define IsEquivalence for ℕ
isEquivalenceNat : IsEquivalence {A = ℕ} _≡_
isEquivalenceNat = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

-- Step 2: Define IsDecEquivalence for ℕ
isDecEquivalenceNat : IsDecEquivalence _≡_
isDecEquivalenceNat = record
  { isEquivalence = isEquivalenceNat
  ; _≟_ = _≟_
  }

-- Step 3: Define the DecSetoid for ℕ
natDecSetoid : DecSetoid lzero lzero
natDecSetoid = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; isDecEquivalence = isDecEquivalenceNat
  }

-- Step 4: Example list of natural numbers
myList : List ℕ
myList = 1 ∷ 2 ∷ 3 ∷ []

-- Step 5: Define membership check with implicit DecSetoid
checkMembership : ∀ {S : DecSetoid lzero lzero} →
                  (n : DecSetoid.Carrier S) →
                  (aList : List (DecSetoid.Carrier S)) →
                  Dec (_∈_ (DecSetoid.setoid S) n aList)
checkMembership {S = S} n xs = _∈?_ S n xs

example : Dec (_∈_ (DecSetoid.setoid natDecSetoid) 1 myList)
example = checkMembership {S = natDecSetoid} 1 myList