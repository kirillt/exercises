module Temp where

  open import Data.Bool

  data   False : Set where
  record True  : Set where

  isTrue  : Bool → Set
  isTrue  true  = True
  isTrue  false = False

  isFalse : Bool → Set
  isFalse true  = False
  isFalse false = True
  
  data X : Bool → Set where
    t : (b : Bool) → {_ : isTrue  b} → X b
    f : (b : Bool) → {_ : isFalse b} → X b

  open import Data.Nat
    
  isZero : ℕ → Bool
  isZero zero = true
  isZero _    = false
    
  x : (n : ℕ) → X (isZero n)
  x n = {!!} -- can't introduce 'with' clause

  y : (b : Bool) → X b
  y b = {!!} -- can't split cases automatically