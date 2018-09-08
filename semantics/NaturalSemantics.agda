{-# OPTIONS --no-termination-check #-}

module NaturalSemantics where

  open import Syntax
  open import Evaluation
  open import Data.Maybe

  record True  : Set where
  data   False : Set where

  open import Data.Bool  
  open import Relation.Binary.PropositionalEquality

  trueIsTrue : {x : Bool} → x ≡ true → T x
  trueIsTrue refl = _

  falseIsNotTrue : {x : Bool} → x ≡ false → T (not x)
  falseIsNotTrue refl = trueIsTrue (cong not refl)
 
  data Transition (s₁ : State) : S → State → Set where
    [skip]   :             Transition s₁   skip                             s₁
    [assign] : ∀ {k v } → Transition s₁ (assign k v) ((k , s₁ [[ v ]]) |> s₁)
    [comp]   : ∀ {s₂ s₃ p₁ p₂} → Transition s₁       p₁     s₂
                                  → Transition s₂       p₂     s₃
                                  → Transition s₁ (comp p₁ p₂) s₃
    [if-t]   : ∀ {s₂ b p₁ p₂} → T (     s₁ << b >> )
                                 → Transition   s₁ p₁ s₂
                                 → Transition   s₁ (branch b p₁ p₂) s₂
    [if-f]   : ∀ {s₂ b p₁ p₂} → T (not (s₁ << b >>))
                                 → Transition   s₁ p₂ s₂
                                 → Transition   s₁ (branch b p₁ p₂) s₂
    [while-t] : ∀ {s₂ s₃ p} → (b : B) → T (     s₁ << b >> )
                              → Transition s₁ p s₂
                              → Transition s₂ (while b p) s₃
                              → Transition s₁ (while b p) s₃
    [while-f] : ∀ {   p} → (b : B) → T (not (s₁ << b >>))
                         → Transition s₁ (while b p) s₁

  record Interpretation (s₁ : State) (p : S) : Set where
    constructor I_,_I
    field
      state      : State
      transition : Transition s₁ p state

  interpret : (s : State) → (p : S) → Interpretation s p
  interpret s₁ (skip           ) = I s₁ , [skip] I
  interpret s₁ (assign   k   v ) = I (k , (s₁ [[ v ]])) |> s₁ , [assign] I
  interpret s₁ (comp     p₁ p₂) with interpret s₁ p₁
  ... | I s₂ , tr₁ I with interpret s₂ p₂
  ... | I s₃ , tr₂ I = I s₃ , [comp] tr₁ tr₂ I
  interpret s₁ (branch b p₁ p₂) with s₁ << b >> | inspect (_<<_>> s₁) b | interpret s₁ p₁ | interpret s₁ p₂
  ... | true  | Reveal_is_.[_] e | I s₂₁ , tr₁ I | I s₂₂ , tr₂ I = I s₂₁ , [if-t] (trueIsTrue e) tr₁ I
  ... | false | Reveal_is_.[_] e | I s₂₁ , tr₁ I | I s₂₂ , tr₂ I = I s₂₂ , [if-f] (falseIsNotTrue e) tr₂ I
  interpret s₁ (while  b p     ) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | false | Reveal_is_.[_] e = I s₁ , [while-f] b (falseIsNotTrue e) I
  ... | true  | Reveal_is_.[_] e with interpret s₁ p
  ... | I s₂ , tr₁ I with interpret s₂ (while b p)
  ... | I s₃ , tr₂ I = I s₃ , [while-t] b (trueIsTrue e) tr₁ tr₂ I