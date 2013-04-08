module StructuralSemantics where

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
  
  record Control : Set where
    constructor [>_,_<]
    field
      state   : State
      program : Maybe S

  data Transition (s₁ : State) : S → Control → Set where
    [skip]    :             Transition s₁   skip       [>                      s₁ , nothing <]
    [assign]  : ∀ {k v } → Transition s₁ (assign k v) [> (k , s₁ [[ v ]]) |> s₁ , nothing <]
    [comp-j]  : ∀ {s₂ p₁ p₂ p₃} → Transition s₁       p₁     [> s₂ , just       p₃      <]
                                   → Transition s₁ (comp p₁ p₂) [> s₂ , just (comp p₃ p₂) <]
    [comp-n]  : ∀ {s₂ p₁ p₂    } → Transition s₁       p₁     [> s₂ , nothing <]
                                   → Transition s₁ (comp p₁ p₂) [> s₂ , just p₂ <]
    [if-t]    : ∀ (b : B) (p₁ p₂ : S) → T (     s₁ << b >> )
                                        → Transition   s₁ (branch b p₁ p₂) [> s₁ , just p₁ <]
    [if-f]    : ∀ (b : B) (p₁ p₂ : S) → T (not (s₁ << b >>))
                                        → Transition   s₁ (branch b p₁ p₂) [> s₁ , just p₂ <]
    [while-t] : ∀ (b : B) (p      : S) → T (     s₁ << b >> )
                                        → Transition s₁ (while b p) [> s₁ , just p <]
    [while-f] : ∀ (b : B) (p      : S) → T (not (s₁ << b >>))
                                       → Transition s₁ (while b p) [> s₁ , nothing <]

  record Interpretation (s₁ : State) (p : S) : Set where
    constructor I_,_I
    field
      control    : Control
      transition : Transition s₁ p control

  interpret : (s : State) → (p : S) → Interpretation s p
  interpret s₁ (skip           ) = I [> s₁ , nothing <] , [skip] I
  interpret s₁ (assign   k   v ) = I [> (k , (s₁ [[ v ]])) |> s₁ , nothing <] , [assign] I
  interpret s₁ (comp     p₁ p₂) with interpret s₁ p₁
  ... | I [> s , just p₃ <] , tr I = I [> s , just (comp p₃ p₂) <] , [comp-j] tr I
  ... | I [> s , nothing <] , tr I = I [> s , just p₂ <] , [comp-n] tr I
  interpret s₁ (branch b p₁ p₂) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | true  | Reveal_is_.[_] e = I [> s₁ , just p₁ <] , [if-t] b p₁ p₂ (trueIsTrue     e) I
  ... | false | Reveal_is_.[_] e = I [> s₁ , just p₂ <] , [if-f] b p₁ p₂ (falseIsNotTrue e) I
  interpret s₁ (while  b p     ) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | true  | Reveal_is_.[_] e = I [> s₁ , just p  <] , [while-t] b p (trueIsTrue     e) I
  ... | false | Reveal_is_.[_] e = I [> s₁ , nothing <] , [while-f] b p (falseIsNotTrue e) I
