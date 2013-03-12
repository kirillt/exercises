module SortedList where

    import Level
    open import IO
    open import Function
    open import Data.Bool
    open import Data.Maybe
    open import Data.List
    open import Data.String
    open import Data.Product
    open import Relation.Nullary.Core

    -- Abstract Data Type -------------------------------------------------------------------------------

    module Core (a : Level.Level) (A : Set a) (_≤_ : A → A → Set a) (_≤?_ : ∀ x y → Dec (x ≤ y)) where

        data Sorted : List A → (Set a) where
            base : Sorted []
            sing : ∀ {x} → Sorted (x ∷ [])
            step : ∀ {x y ts} → x ≤ y → Sorted (y ∷ ts) → Sorted (x ∷ y ∷ ts)

        sorted?  : (list : List A) → Dec (Sorted list)
        sorted?          []  = yes base
        sorted? (    x ∷ []) = yes sing
        sorted? (x ∷ y ∷ ts) with x ≤? y | sorted? (y ∷ ts)
        ... | yes x≤y | yes sorted = yes (step x≤y sorted)
        ... | yes x≤y | no ¬sorted = no λ { (step a b) → ¬sorted b }
        ... | no ¬x≤y | _          = no λ { (step a b) → ¬x≤y    a }

        data SortedList : (Set a) where
            pack : (list : List A) → Sorted list → SortedList

        tosorted : (list : List A) → Maybe SortedList
        tosorted      []  = just (pack      []  base)
        tosorted (x ∷ []) = just (pack (x ∷ []) sing)
        tosorted xs with sorted? xs
        ... | yes proof = just (pack xs proof)
        ... | no      _ = sort xs
            where
                sort : (list : List A) → Maybe SortedList
                sort xs = nothing --TODO

        insert  : SortedList → A → Maybe SortedList
        insert (pack          []              base ) z = just (pack (z ∷ []) sing)
        insert (pack     (x ∷ [])             sing ) z with x ≤? z | z ≤? x
        ... | yes x≤z | _       = just (pack (x ∷ z ∷ []) (step x≤z sing))
        ... | _       | yes z≤x = just (pack (z ∷ x ∷ []) (step z≤x sing))
        ... | no ¬x≤z | no ¬z≤x = nothing
        insert (pack (x ∷ y ∷ ts) (step x≤y sorted)) z with z ≤? x
        ... | yes z≤x = just (pack (z ∷ x ∷ y ∷ ts) (step z≤x (step x≤y sorted)))
        ... | no ¬z≤x = consagain (insert (pack (y ∷ ts) sorted) z)
            where
                consagain : Maybe SortedList → Maybe SortedList
                consagain (just list) = insert list x -- DIRTY! Best way: use x≤y and/or some theorems to prove that (x ∷ list) is sorted
                consagain nothing     = nothing

    -----------------------------------------------------------------------------------------------------

    open import Data.Nat
    open Core Level.zero ℕ _≤_ _≤?_

    s?    : (list : List ℕ) → Dec (Sorted list)
    s?    = sorted?
    
    _x_   : ℕ → List ℕ → List ℕ
    a x b = a ∷ b

    list1 : List ℕ
    list1 = 1 ∷ 2 ∷ 3 ∷ []

    list2 : List ℕ
    list2 = 3 ∷ 2 ∷ 1 ∷ []
