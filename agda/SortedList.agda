module SortedList where

    import Level
    open import IO
    open import Function
    open import Data.Nat
    open import Data.Bool
    open import Data.List
    open import Data.String
    open import Data.Product
    open import Relation.Nullary.Core

    -- Abstract Data Type -------------------------------------------------------------------------------

    module Core (a : Level.Level) (A : Set a) (_≤'_ : A → A → Set a) (_≤?'_ : ∀ x y → Dec (x ≤' y)) where

        data Sorted : List A → (Set a) where
            base : Sorted []
            sing : ∀ {x} → Sorted (x ∷ [])
            step : ∀ {x y ts} → x ≤' y → Sorted (y ∷ ts) → Sorted (x ∷ y ∷ ts)

        sorted?  : (list : List A) → Dec (Sorted list)
        sorted?          []  = yes base
        sorted? (    x ∷ []) = yes sing
        sorted? (x ∷ y ∷ ts) with x ≤?' y | sorted? (y ∷ ts)
        ... | yes x≤y | yes sorted = yes (step x≤y sorted)
        ... | yes x≤y | no ¬sorted = no λ { (step a b) → ¬sorted b }
        ... | no ¬x≤y | _          = no λ { (step a b) → ¬x≤y    a }

    -----------------------------------------------------------------------------------------------------

    open Core Level.zero ℕ _≤_ _≤?_

    s?    : (list : List ℕ) → Dec (Sorted list)
    s?    = sorted?
    
    _x_   : ℕ → List ℕ → List ℕ
    a x b = a ∷ b

    list1 : List ℕ
    list1 = 1 ∷ 2 ∷ 3 ∷ []

    list2 : List ℕ
    list2 = 3 ∷ 2 ∷ 1 ∷ []
