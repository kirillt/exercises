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

    module Core (a : Level.Level) (A : Set a) (_≤_ : A → A → Set a) (_≤?_ : ∀ x y → Dec (x ≤ y)) (≰⇒≤ : {a b : A} → (¬(a ≤ b)) → (b ≤ a)) where


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


        insert  : SortedList → A → SortedList
        insert (pack list sorted) z = insert-unpacked list sorted z
            where
                insert-unpacked : (list : List A) → Sorted list → A → SortedList

                insert-unpacked      []  base z = pack (z ∷ []) sing

                insert-unpacked (x ∷ []) sing z with x ≤? z
                ... | yes x≤z = pack (x ∷ z ∷ []) (step       x≤z  sing)
                ... | no ¬x≤z = pack (z ∷ x ∷ []) (step (≰⇒≤ ¬x≤z) sing)

                insert-unpacked (x ∷ y ∷ ts) (step x≤y sorted) z with z ≤? x
                ... | yes z≤x = pack (z ∷ x ∷ y ∷ ts) (step z≤x (step x≤y sorted))
                ... | no ¬z≤x = consagain (insert-unpacked (y ∷ ts) sorted z)
                    where
                        consagain : SortedList → SortedList
                        consagain (pack      []  _      ) = pack (    x ∷ []) sing
                        consagain (pack (q ∷ ss) sorted') = pack (x ∷ q ∷ ss) (step {!!} sorted')

    -----------------------------------------------------------------------------------------------------

    open import Data.Nat
    open import Data.Nat.Properties

    open import Relation.Binary
    open DecTotalOrder Data.Nat.decTotalOrder using () renaming (trans to ≤-trans)

    ≰⇒≤   : {a b : ℕ} → (a ≰ b) → (b ≤ a)
    ≰⇒≤ {a} {b} a≰b = let sb≤a = ≰⇒> a≰b in lower (≤-trans sb≤a a≤sa)
        where
            a≤sa  : {x : ℕ} → x ≤ suc x
            a≤sa {zero } = z≤n
            a≤sa {suc y} = s≤s (a≤sa {y})

            lower : {x y : ℕ} → (suc x ≤ suc y) → (x ≤ y)
            lower (s≤s px≤py) = px≤py

    open Core Level.zero ℕ _≤_ _≤?_ ≰⇒≤

    list1 : List ℕ
    list1 = 1 ∷ 2 ∷ 3 ∷ []

    list2 : List ℕ
    list2 = 3 ∷ 2 ∷ 1 ∷ []

