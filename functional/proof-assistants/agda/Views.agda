module Views where

  open import Data.Nat
  open import Data.List

  module Parity where

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

  module ListsAndPredicates where

    open import Function
    open import Data.Bool

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
      found     : (pre post : List A) → (x : A) → satisfies p x → Find p (pre ++ x ∷ post)
      not-found : {xs    : List A} → All (satisfies (not ∘ p)) xs → Find p xs

    find : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
    find _      []  = not-found [all]
    find p (x ∷ xs) with p x | inspect p x
    ... | true  | Reveal_is_.[_] eq = found [] xs x (trueIsTrue eq)
    ... | false | Reveal_is_.[_] eq with find p xs
    find p (x ∷ xs) | false | Reveal_is_.[_] eq | not-found        proof = not-found ((falseIsFalse eq) :all: proof)
    find p (x ∷ ._) | false | Reveal_is_.[_] eq | found pre post y proof = found (x ∷ pre) post y proof

  module ListsAndIndexing where

    data _∈_ {A : Set} (x : A) : List A → Set where
        hd : {xs : List A} → x ∈ xs
        tl : {ys : List A} → x ∈ ys → {y : A} → x ∈ (y ∷ ys)
        
    index : {A : Set} → {xs : List A} → {x : A} → x ∈ xs → ℕ
    index  hd       = zero
    index (tl rest) = suc (index rest)

    data Lookup {A : Set} (xs : List A) : ℕ → Set where
      inside  : (x : A) → (x∈xs : x ∈ xs) → Lookup xs (index x∈xs)
      outside : {n : ℕ} → Lookup xs (length xs + n)

    _!_ : {A : Set} → (xs : List A) → (i : ℕ) → Lookup xs i
    (    []) !      i  = outside
    (x ∷ xs) !      0  = inside x hd
    (x ∷ xs) ! suc i with xs ! i
    (x ∷ xs) ! suc .(index   proof) | inside  y proof = inside y (tl proof)
    (x ∷ xs) ! suc .(length xs + i) | outside {i}     = outside
    
    