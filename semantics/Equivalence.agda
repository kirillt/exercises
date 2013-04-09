module Equivalence where

  open import NaturalSemantics    renaming (Transition  to Transition-NS ; interpret to interpret-ns )
  open import StructuralSemantics renaming (Transition* to Transition-SOS; interpret to interpret-sos)

  open Control

  open import Syntax
  open import Evaluation

  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality

  sos≡ns : (s : State) → (p : S) → ∀ {s-sos s-ns}
    → (tr-sos : Transition-SOS s p s-sos) → (tr-ns : Transition-NS s p s-ns)
    → s-sos ≡ s-ns
  sos≡ns s .(comp p₁ p₂) (cons ([comp-j] {s₂} {p₁} {p₂} y) tr-sos*) ([comp] y' y0) = {!!}
  sos≡ns s .(comp p₁ p₂) (cons {s₂} {s₃} {.(comp p₁ p₂)} {p₂} ([comp-n] {.s₂} {p₁} y) tr-sos*) ([comp] y' y0) = {!!}
  sos≡ns .s₂ .(branch b p₂ p₂') (cons {s₂} {s₃} {.(branch b p₂ p₂')} {p₂} ([if-t] b .p₂ p₂' y) tr-sos*) ([if-t] y' y0) = sos≡ns s₂ p₂ tr-sos* y0
  sos≡ns .s₂ .(branch b p₂ p₂') (cons {s₂} {s₃} {.(branch b p₂ p₂')} {p₂} ([if-t] b .p₂ p₂' y) tr-sos*) ([if-f] y' y0) = {!!}
  sos≡ns .s₂ .(branch b p₁ p₂) (cons {s₂} {s₃} {.(branch b p₁ p₂)} {p₂} ([if-f] b p₁ .p₂ y) tr-sos*) ([if-t] y' y0) = {!!}
  sos≡ns .s₂ .(branch b p₁ p₂) (cons {s₂} {s₃} {.(branch b p₁ p₂)} {p₂} ([if-f] b p₁ .p₂ y) tr-sos*) ([if-f] y' y0) = sos≡ns s₂ p₂ tr-sos* y0
  sos≡ns .s₂ .(while b p₂) (cons {s₂} {s₃} {.(while b p₂)} {p₂} ([while-t] b .p₂ y) tr-sos*) ([while-t] .b y' y0 y1) = {!!}
  sos≡ns .s-ns .(while b p₂) {.s₃} {s-ns} (cons {.s-ns} {s₃} {.(while b p₂)} {p₂} ([while-t] b .p₂ y) tr-sos*) ([while-f] .b y') = {!!}
  sos≡ns .s-ns .skip {.s-ns} {s-ns} (base [skip]) [skip] = refl
  sos≡ns s .(assign k v) (base ([assign] {k} {v})) [assign] = refl
  sos≡ns .s-sos .(while b p) {s-sos} (base ([while-f] b p y)) ([while-t] .b y' y0 y1) = {!!}
  sos≡ns .s-ns .(while b p) {.s-ns} {s-ns} (base ([while-f] b p y)) ([while-f] .b y') = refl