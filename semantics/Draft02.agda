module Draft02 where

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

--  falseIsFalse : {x : Bool} → x ≡ false → isFalse x
--  falseIsFalse refl = _
  
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

  data Transition (s₁ : State) : S → Control → Set where
    [skip]   :             Transition s₁   skip       [>            s₁ , nothing <]
    [assign] : ∀ {k v } → Transition s₁ (assign k v) [> (k , v) |> s₁ , nothing <]
    [comp-j] : ∀ {s₂ p₁ p₂ p₃} → Transition s₁       p₁     [> s₂ , just       p₃      <]
                                  → Transition s₁ (comp p₁ p₂) [> s₂ , just (comp p₃ p₂) <]
    [comp-n] : ∀ {s₂ p₁ p₂    } → Transition s₁       p₁     [> s₂ , nothing <]
                                  → Transition s₁ (comp p₁ p₂) [> s₂ , just p₂ <]
--    [if-t]   : ∀ (b : B) (p₁ p₂ : S) → isTrue (     s₁ << b >> )
--                                         → Transition s₁ (branch b p₁ p₂) [> s₁ , just p₁ <]
--    [if-f]   : ∀ (b : B) (p₁ p₂ : S) → isTrue (not (s₁ << b >>))
--                                         → Transition s₁ (branch b p₁ p₂) [> s₁ , just p₂ <]

  record Interpretation (s₁ : State) (p : S) : Set where
    constructor I_,_I
    field
      control    : Control
      transition : Transition s₁ p control

  interpret : (s : State) → (p : S) → Interpretation s p
  interpret s₁  skip             = {!!}
  interpret s₁ (assign   k   v ) = {!!}
  interpret s₁ (comp     p₁ p₂) = {!!}
  interpret s₁ (branch b p₁ p₂) = {!!}
  interpret s₁ (while  b p     ) = {!!}