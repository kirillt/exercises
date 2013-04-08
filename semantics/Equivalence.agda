module Equivalence where

  open import NaturalSemantics    renaming (Transition to Transition-NS ; interpret to interpret-ns )
  open import StructuralSemantics renaming (Transition to Transition-SOS; interpret to interpret-sos)

  open Control

  open import Syntax
  open import Evaluation

  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality

  sos≡ns : (s : State) → (p : S) → ∀ {s-sos s-ns}
    → (tr-sos : Transition-SOS s p [> s-sos , nothing <]) → (tr-ns : Transition-NS s p s-ns)
    → s-sos ≡ s-ns
  sos≡ns .s-ns .skip {.s-ns} {s-ns} [skip] [skip] = refl
  sos≡ns s .(assign k v) ([assign] {k} {v}) [assign] = refl
  sos≡ns .s-sos .(while b p) {s-sos} ([while-f] b p y) tr-ns = {!!}