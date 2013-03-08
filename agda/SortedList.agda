module SortedList where

    import Level
    open import IO
    open import Function
    open import Data.Nat
    open import Data.Bool
    open import Data.List
    open import Data.String

    asclist : List ℕ
    asclist = 1 ∷ 2 ∷ 3 ∷ []

    deslist : List ℕ
    deslist = 3 ∷ 2 ∷ 1 ∷ []

    Order : ∀ {a} → Set a → Set a
    Order A = A → A → Bool

    ascending : Order ℕ
    ascending 0 _ = true
    ascending _ 0 = false
    ascending (suc n) (suc m) = ascending n m

    descending : Order ℕ
    descending x y = ascending y x

    verify : ∀ {a} → ∀ {A : Set a} → Order A → List A → Bool
    verify         _      []    = true
    verify {a} {A} o (x ∷ list) = (verify' x list)
        where
            verify' : A → List A → Bool
            verify' x      []    = true
            verify' x (y ∷ list) = o x y ∧ (verify' y list)
