module SortedList where

    import Level
    open import IO
    open import Data.Nat
    open import Data.Bool

    open import Relation.Binary

    Order = Rel ℕ Level.zero

    ascending : Order
    ascending l r = l < r

    data SortedList  (A : Set) (O : Order) : Set where
        Nil  : SortedList A O 
        Cons : A -> SortedList A O -> SortedList A O

    main = run (putStrLn "")
