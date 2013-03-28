module Draft01 where

  open import Data.Nat
  open import Data.List
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

  _<<_>> : State → B → Bool
  s << const x   >> = x
  s << conj  x y >> = (s << x >>) ∧ (s << y >>)
  s << neg   x   >> = not (s << x >>)
  s << le    x y >> = le-nat (s [[ x ]]) (s [[ y ]])
  s << eq    x y >> = eq-nat (s [[ x ]]) (s [[ y ]])
    
  data S : Set where
    skip  : S
    comp  : S → S → S
    as    : Variable → ℕ → S
    if-then-else : B → S → S → S
    while : B → S → S

  data Transition (s₁ : State) : (s₂ : State) → S → Set where
    [skip] : Transition s₁ s₁ skip
    [as]   : ∀ {v n} → Transition s₁ ((v , n) |> s₁) (as v n)
    [comp] : ∀ {o₁ o₂ s₂ s₃} → Transition s₁ s₂ o₁ → Transition s₂ s₃ o₂ → Transition s₁ s₃ (comp o₁ o₂)
    
    [ift]  : ∀ {o₁ o₂ s₂ b} → isTrue  (s₁ << b >>) →
                   Transition s₁ s₂ o₁ → Transition s₁ s₂ (if-then-else b o₁ o₂)
    [iff]  : ∀ {o₁ o₂ s₂ b} → isFalse (s₁ << b >>) →
                   Transition s₁ s₂ o₂ → Transition s₁ s₂ (if-then-else b o₁ o₂)
                   
    [wlt]  : ∀ {o s₂ b} → isTrue (s₁ << b >>) →
                   Transition s₁ s₂ o → Transition s₁ s₂ (while b o)
    [wlf]  : ∀ {o b} → isFalse (s₁ << b >>) →
                   Transition s₁ s₁ (while b o)

  record Interpretation (s₁ : State) (p : S) : Set where
    constructor _,_
    field
        state      : State
        transition : Transition s₁ state p

  open Interpretation

  interpret : (p : S) → (s₁ : State) → Interpretation s₁ p
  
--  interpret skip s = result s [skip]
  interpret skip s = {!!}

--  interpret (comp y₁ y₂) s₁ with interpret y₁ s₁
--  ... | result s₂ tr₁ with interpret y₂ s₂
--  ...     | result s₃ tr₂ = result s₃ ([comp] tr₁ tr₂)

--  interpret (comp y₁ y₂) s₁ = (state (interpret y₂ (state (interpret y₁ s₁)))) ,
--                                ([comp]
--                                    (transition (interpret y₁ s₁))
--                                    (transition (interpret y₂ (state (interpret y₁ s₁)))))

  interpret (comp y₁ y₂) s₁ = {!!}
  
--  interpret (as y y') s = result ((y , y') |> s) [as]
  interpret (as y y') s = {!!}
  
  interpret (if-then-else b o₁ o₂) s with s << b >>
  ... | true  = {!!}
  ... | false = {!!}
  
  interpret (while b o) s with s << b >>
  ... | true  = {!!}
  ... | false = {!!}
