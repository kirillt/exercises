module Syntax where

  open import Data.Nat

  V = ℕ

  data A : Set where
    const : ℕ → A
    plus  : A → A → A
    star  : A → A → A
    var   : V → A
    
  open import Data.Bool

  data B : Set where
    const : Bool → B
    conj  : B → B → B
    disj  : B → B → B
    neg   : B → B
    lt    : A → A → B
    gt    : A → A → B
    eq    : A → A → B

  data S : Set where
    skip   : S
    comp   : S → S → S
    assign : V → A → S
    branch : B → S → S → S
    while  : B → S → S
