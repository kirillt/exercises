module Draft03 where

  open import Data.Nat
  open import Data.List hiding (reverse)
  open import Data.Bool
  open import Data.String
  open import Relation.Binary.PropositionalEquality

  eq-nat : ℕ → ℕ → Bool
  eq-nat  zero    zero   = true
  eq-nat  zero    _      = false
  eq-nat  _       zero   = false
  eq-nat (suc n) (suc m) = eq-nat n m

  le-nat : ℕ → ℕ → Bool
  le-nat  zero    _      = true
  le-nat (suc _)  zero   = false
  le-nat (suc n) (suc m) = le-nat n m

  Variable = ℕ

  record Binding : Set where
    constructor _,_
    field
      key   : Variable
      value : ℕ

  State = List Binding

  _|>_ : Binding → State → State
  kv      |>                [] = kv ∷ []
  (k , v) |>   ((k' , v') ∷ ts) with eq-nat k k'
  ... | true  = (k  , v ) ∷            ts
  ... | false = (k' , v') ∷ (k , v) |> ts

  _<|_ : State → Variable → ℕ
  []               <| _ = 0
  ((k' , v') ∷ ts) <| k with eq-nat k k'
  ... | true  = v'
  ... | false = ts <| k

  data A : Set where
    const : ℕ → A
    plus  : A → A → A
    star  : A → A → A
    var   : Variable → A

  _[[_]] : State → A → ℕ
  s [[ const x   ]] = x
  s [[ plus  x y ]] = (s [[ x ]]) + (s [[ y ]])
  s [[ star  x y ]] = (s [[ x ]]) * (s [[ y ]])
  s [[ var   x   ]] = s <| x
    
  data B : Set where
    const : Bool → B
    conj  : B → B → B
    neg   : B → B
    le    : A → A → B
    eq    : A → A → B

  data   False : Set where
  record True  : Set where

  isTrue : Bool → Set
  isTrue true = True
  isTrue _    = False

  isFalse : Bool → Set
  isFalse false = False
  isFalse _     = True

  open import Relation.Binary.PropositionalEquality

  trueIsTrue : {x : Bool} → x ≡ true → isTrue x
  trueIsTrue refl = _

  falseIsNotTrue : {x : Bool} → x ≡ false → isTrue (not x)
  falseIsNotTrue refl = trueIsTrue (cong not refl)
  
  _<<_>> : State → B → Bool
  s << const x   >> = x
  s << conj  x y >> = (s << x >>) ∧ (s << y >>)
  s << neg   x   >> = not (s << x >>)
  s << le    x y >> = le-nat (s [[ x ]]) (s [[ y ]])
  s << eq    x y >> = eq-nat (s [[ x ]]) (s [[ y ]])
    
  data S : Set where
    skip   : S
    comp   : S → S → S
    assign : Variable → ℕ → S
    branch : B → S → S → S
    while  : B → S → S

  open import Data.Maybe

  record Control : Set where
    constructor [>_,_<]
    field
      state   : State
      program : Maybe S

  data Transition-SS (s₁ : State) : S → Control → Set where
    [skip]    :             Transition-SS s₁   skip       [>            s₁ , nothing <]
    [assign]  : ∀ {k v } → Transition-SS s₁ (assign k v) [> (k , v) |> s₁ , nothing <]
    [comp-j]  : ∀ {s₂ p₁ p₂ p₃} → Transition-SS s₁       p₁     [> s₂ , just       p₃      <]
                                   → Transition-SS s₁ (comp p₁ p₂) [> s₂ , just (comp p₃ p₂) <]
    [comp-n]  : ∀ {s₂ p₁ p₂    } → Transition-SS s₁       p₁     [> s₂ , nothing <]
                                   → Transition-SS s₁ (comp p₁ p₂) [> s₂ , just p₂ <]
    [if-t]    : ∀ (b : B) (p₁ p₂ : S) → isTrue (     s₁ << b >> )
                                        → Transition-SS   s₁ (branch b p₁ p₂) [> s₁ , just p₁ <]
    [if-f]    : ∀ (b : B) (p₁ p₂ : S) → isTrue (not (s₁ << b >>))
                                        → Transition-SS   s₁ (branch b p₁ p₂) [> s₁ , just p₂ <]
    [while-t] : ∀ (b : B) (p      : S) → isTrue (     s₁ << b >> )
                                        → Transition-SS s₁ (while b p) [> s₁ , just p <]
    [while-f] : ∀ (b : B) (p      : S) → isTrue (not (s₁ << b >>))
                                       → Transition-SS s₁ (while b p) [> s₁ , nothing <]

  record Interpretation-SS (s₁ : State) (p : S) : Set where
    constructor I_,_I
    field
      control    : Control
      transition : Transition-SS s₁ p control

  interpret-sos : (s : State) → (p : S) → Interpretation-SS s p
  interpret-sos s₁ (skip           ) = I [> s₁ , nothing <] , [skip] I
  interpret-sos s₁ (assign   k   v ) = I [> (k , v) |> s₁ , nothing <] , [assign] I
  interpret-sos s₁ (comp     p₁ p₂) with interpret-sos s₁ p₁
  ... | I [> s , just p₃ <] , tr I = I [> s , just (comp p₃ p₂) <] , [comp-j] tr I
  ... | I [> s , nothing <] , tr I = I [> s , just p₂ <] , [comp-n] tr I
  interpret-sos s₁ (branch b p₁ p₂) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | true  | Reveal_is_.[_] e = I [> s₁ , just p₁ <] , [if-t] b p₁ p₂ (trueIsTrue     e ) I
  ... | false | Reveal_is_.[_] e = I [> s₁ , just p₂ <] , [if-f] b p₁ p₂ (falseIsNotTrue e ) I
  interpret-sos s₁ (while  b p     ) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | true  | Reveal_is_.[_] e = I [> s₁ , just p <] , [while-t] b p (trueIsTrue e) I
  ... | false | Reveal_is_.[_] e = I [> s₁ , nothing <] , [while-f] b p (falseIsNotTrue e) I

  data Transition-NS (s₁ : State) : S → State → Set where
    [skip]   :             Transition-NS s₁   skip                   s₁
    [assign] : ∀ {k v } → Transition-NS s₁ (assign k v) ((k , v) |> s₁)
    [comp]   : ∀ {s₂ s₃ p₁ p₂} → Transition-NS s₁       p₁     s₂
                                  → Transition-NS s₂       p₂     s₃
                                  → Transition-NS s₁ (comp p₁ p₂) s₃
    [if-t]   : ∀ {s₂ b p₁ p₂} → isTrue (     s₁ << b >> )
                                 → Transition-NS   s₁ p₁ s₂
                                 → Transition-NS   s₁ (branch b p₁ p₂) s₂
    [if-f]   : ∀ {s₂ b p₁ p₂} → isTrue (not (s₁ << b >>))
                                 → Transition-NS   s₁ p₂ s₂
                                 → Transition-NS   s₁ (branch b p₁ p₂) s₂
    [while-t] : ∀ {s₂ s₃ p} → (b : B) → isTrue (     s₁ << b >> )
                              → Transition-NS s₁ p s₂
                              → Transition-NS s₂ (while b p) s₃
                              → Transition-NS s₁ (while b p) s₃
    [while-f] : ∀ {   p} → (b : B) → isTrue (not (s₁ << b >>))
                         → Transition-NS s₁ (while b p) s₁

  record Interpretation-NS (s₁ : State) (p : S) : Set where
    constructor I_,_I
    field
      state      : State
      transition : Transition-NS s₁ p state

  interpret-ns : (s : State) → (p : S) → Interpretation-NS s p
  interpret-ns s₁ (skip           ) = I s₁ , [skip] I
  interpret-ns s₁ (assign   k   v ) = I (k , v) |> s₁ , [assign] I
  interpret-ns s₁ (comp     p₁ p₂) with interpret-ns s₁ p₁
  ... | I s₂ , tr₁ I with interpret-ns s₂ p₂
  ... | I s₃ , tr₂ I = I s₃ , [comp] tr₁ tr₂ I
  interpret-ns s₁ (branch b p₁ p₂) with s₁ << b >> | inspect (_<<_>> s₁) b | interpret-ns s₁ p₁ | interpret-ns s₁ p₂
  ... | true  | Reveal_is_.[_] e | I s₂₁ , tr₁ I | I s₂₂ , tr₂ I = I s₂₁ , [if-t] (trueIsTrue e) tr₁ I
  ... | false | Reveal_is_.[_] e | I s₂₁ , tr₁ I | I s₂₂ , tr₂ I = I s₂₂ , [if-f] (falseIsNotTrue e) tr₂ I
  interpret-ns s₁ (while  b p     ) with s₁ << b >> | inspect (_<<_>> s₁) b
  ... | false | Reveal_is_.[_] e = I s₁ , [while-f] b (falseIsNotTrue e) I
  ... | true  | Reveal_is_.[_] e with interpret-ns s₁ p
  ... | I s₂ , tr₁ I with interpret-ns s₂ (while b p)
  ... | I s₃ , tr₂ I = I s₃ , [while-t] b (trueIsTrue e) tr₁ tr₂ I

  open Control

  sos≡ns : (s : State) → (p : S) → ∀ {s-sos s-ns}
    → (tr-sos : Transition-SS s p [> s-sos , nothing <]) → (tr-ns : Transition-NS s p s-ns)
    → s-sos ≡ s-ns
  sos≡ns .s-ns .skip {.s-ns} {s-ns} [skip] [skip] = refl
  sos≡ns s .(assign k v) ([assign] {k} {v}) [assign] = refl
  sos≡ns .s-sos .(while b p) {s-sos} ([while-f] b p y) ([while-t] .b y' y0 y1)
    with s-sos << b >> | inspect (_<<_>> s-sos) b
  ... | true  | Reveal_is_.[_] e = {!!}
  ... | false | Reveal_is_.[_] e = {!!}
  sos≡ns .s-ns .(while b p) {.s-ns} {s-ns} ([while-f] b p y) ([while-f] .b y') = refl
