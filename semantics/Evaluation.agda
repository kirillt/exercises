module Evaluation where

  open import Syntax

  open import Data.Nat renaming (_≟_ to _≡?_)
  
  record Binding : Set where
    constructor _,_
    field
      key   : V
      value : ℕ

  open import Data.List
      
  State = List Binding

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  
  _|>_ : Binding → State → State
  kv      |>                [] = kv ∷ []
  (k , v) |>   ((k' , v') ∷ ts) with k ≡? k'
  ... | yes _ = (k  , v ) ∷            ts
  ... | no  _ = (k' , v') ∷ (k , v) |> ts

  _<|_ : State → V → ℕ
  []               <| _ = 0
  ((k' , v') ∷ ts) <| k with k ≡? k'
  ... | yes _ = v'
  ... | no  _ = ts <| k

  _[[_]] : State → A → ℕ
  s [[ const x   ]] = x
  s [[ plus  x y ]] = (s [[ x ]]) + (s [[ y ]])
  s [[ star  x y ]] = (s [[ x ]]) * (s [[ y ]])
  s [[ var   x   ]] = s <| x

  open import Data.Bool

  open import Relation.Binary
  
  _<<_>> : State → B → Bool
  s << const x   >> = x
  s << conj  x y >> = (s << x >>) ∧ (s << y >>)
  s << disj  x y >> = (s << x >>) ∨ (s << y >>)
  s << neg   x   >> = not (s << x >>)
  s << lt    x y >> with ((s [[ x ]]) ≤? (s [[ y ]]))
  ... | yes _ = true
  ... | no  _ = false
  s << gt    x y >> with ((s [[ x ]]) ≤? (s [[ y ]]))
  ... | yes _ = true
  ... | no  _ = false
  s << eq    x y >> with ((s [[ x ]]) ≡? (s [[ y ]]))
  ... | yes _ = true
  ... | no  _ = false
