module Monad where

  open import Level
  open import Data.List hiding (mapM)

  1l : Level.Level
  1l = Level.suc Level.zero

  -- Monad (similar to internal type-class representation in haskell)

  record Monad (M : Set → Set) : Set 1l where
    field
      _>>=_  : {A B : Set} → M A → (A → M B) → M B
      return : {  A : Set} → A → M A

    --Example

    mapM : {A B : Set} → (A → M B) → List A → M (List B)
    mapM f      []  = return []
    mapM f (h ∷ ts) = f h       >>= \y  →
                      mapM f ts >>= \ys →
                      return (y ∷ ys)

  -- List Monad (similar to internal instance representation in haskell)

  list-monad : Monad List
  list-monad = record{ _>>=_ = list-bind ; return = list-return }
    where
      list-bind   : {A B : Set} → List A → (A → List B) → List B
      list-bind      []  _ = []
      list-bind (h ∷ ts) f = f h ++ list-bind ts f

      list-return : {  A : Set} → A → List A
      list-return a = a ∷ []

  -- Test

  open import Data.Product hiding (map)

  cartesian-product : {A B : Set} → List A → List B → List (A × B)
  cartesian-product ns ms =
    let open Monad list-monad in
      ns >>= λ n → map (λ m → n , m) ms