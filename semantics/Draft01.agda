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

  data Transition : S → State → State → Set where
    [skip] : ∀ {s} → Transition skip s s
    [as]   : ∀ {v n s} → Transition (as v n) s ((v , n) |> s)
    [comp] : ∀ {o₁ o₂ s₁ s₂ s₃} → Transition o₁ s₁ s₂ → Transition o₂ s₂ s₃ → Transition (comp o₁ o₂) s₁ s₃
    
    [ift]  : ∀ {o₁ o₂ s₁ s₂ b} → isTrue  (s₁ << b >>) →
                   Transition o₁ s₁ s₂ → Transition (if-then-else b o₁ o₂) s₁ s₂
    [iff]  : ∀ {o₁ o₂ s₁ s₂ b} → isFalse (s₁ << b >>) →
                   Transition o₂ s₁ s₂ → Transition (if-then-else b o₁ o₂) s₁ s₂
                   
    [wlt]  : ∀ {o s₁ s₂ b} → isTrue (s₁ << b >>) →
                   Transition o s₁ s₂ → Transition (while b o) s₁ s₂
    [wlf]  : ∀ {o s b} → isFalse (s << b >>) →
                   Transition (while b o) s s

  data Interpretation (p : S) (s₁ : State) : Set where
    result : (s₂ : State) → Transition p s₁ s₂ → Interpretation p s₁

  extract : ∀ {p s₁} → Interpretation p s₁ → State
  extract (result s₂ _) = s₂
  
  interpret : (p : S) → (s₁ : State) → Interpretation p s₁
  
--  interpret skip s = result s [skip]
  interpret skip s = {!!}
  
--  interpret (comp y₁ y₂) s₁ with interpret y₁ s₁
--  ... | result s₂ tr₁ with interpret y₂ s₂
--  ...     | result s₃ tr₂ = result s₃ ([comp] tr₁ tr₂)
  interpret (comp y₁ y₂) s₁ = {!!}
  
--  interpret (as y y') s = result ((y , y') |> s) [as]
  interpret (as y y') s = {!!}
  
  interpret (if-then-else b o₁ o₂) s with s << b >>
  ... | true  = {!!}
  ... | false = {!!}
  
  interpret (while b o) s with s << b >>
  ... | true  = {!!}
  ... | false = {!!}
