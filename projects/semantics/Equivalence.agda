module Equivalence where

  open import NaturalSemantics    renaming
    (Transition to Transition-NS;
     interpret  to interpret-ns)
  open import StructuralSemantics renaming
    (Transition  to Transition-SS;
     Transition* to Transition-SS*;
     interpret to interpret-sos)

  open Control

  open import Syntax
  open import Evaluation

  open import Data.Bool
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality

  sos≡ns : (s : State) → (p : S) → ∀ {s-sos s-ns}
    → (tr-sos : Transition-SS* s p s-sos) → (tr-ns : Transition-NS s p s-ns)
    → s-sos ≡ s-ns
  sos≡ns s p {s-sos} {s-ns} tr-sos tr-ns = {!!}
