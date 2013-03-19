module Views where

  module Parity where

    open import Data.Nat

    data Parity : ℕ → Set where
      even : (k : ℕ) → Parity (    k * 2)
      odd  : (k : ℕ) → Parity (1 + k * 2)

    parity : (n : ℕ) → Parity n
    parity zero = even zero
    parity (suc n) with parity n
    parity (suc .(    k * 2)) | even k = odd       k
    parity (suc .(1 + k * 2)) | odd  k = even (suc k)

    half   : ℕ → ℕ
    half n with parity n
    half .(    k * 2) | even k = k
    half .(1 + k * 2) | odd  k = k

  module Lists where

    open import Function
    open import Data.Bool
    open import Data.List

    data All {A : Set} (P : A → Set) : List A → Set where
      [all]   : All P []
      _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

    data   False : Set where
    record True  : Set where

    isTrue : Bool → Set
    isTrue true  = True
    isTrue false = False
      
    open import Relation.Binary.PropositionalEquality

    trueIsTrue   : {x : Bool} → x ≡ true  → isTrue x
    trueIsTrue   refl = _
      
    falseIsFalse : {x : Bool} → x ≡ false → isTrue (not x)
    falseIsFalse refl = _
      
    satisfies : {A : Set} → (A → Bool) → A → Set
    satisfies p x = isTrue (p x)

    filter-satisfies : {A : Set} → (xs : List A) → (p : A → Bool) → All (satisfies p) (filter p xs)
    filter-satisfies      []  _ = [all]
    filter-satisfies (x ∷ xs) p with p x | inspect p x
    ... | true  | Reveal_is_.[_] eq = (trueIsTrue eq) :all:
                                      filter-satisfies xs p
    ... | false |                _  = filter-satisfies xs p

    data Find {A : Set} (p : A → Bool) : List A → Set where
      found     : (xs zs : List A) → (y : A) → satisfies p y → Find p (xs ++ y ∷ zs)
      not-found : {xs    : List A} → All (satisfies (not ∘ p)) xs → Find p xs

    find : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
    find _      []  = not-found [all]
    find p (x ∷ xs) with p x | inspect p x
    ... | true  | Reveal_is_.[_] eq = found [] xs x (trueIsTrue eq)
    ... | false | Reveal_is_.[_] eq with find p xs
    find p (x ∷ xs) | false | Reveal_is_.[_] eq | not-found        proof = not-found ((falseIsFalse eq) :all: proof)
    find p (x ∷ ._) | false | Reveal_is_.[_] eq | found pre post y proof = found (x ∷ pre) post y proof 