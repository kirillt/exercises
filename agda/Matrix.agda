module Matrix where

  open import Data.Nat
  open import Data.Vec hiding (replicate)

  data Matrix (A : Set) : (n m : ℕ) → Set where
    empty : Matrix A 0 0
    full  : {n m : ℕ} → Vec (Vec A (suc m)) (suc n) → Matrix A (suc n) (suc m)
    -- There are a lot of different [] matrices ∀ {n : ℕ} → (Vec (Vec A n) 0)

  replicate  : {A   : Set} → {n   : ℕ} → A → Vec A n
  replicate  {n = zero } _ = []
  replicate  {n = suc _} a = a ∷ replicate a

  multiapply : {A B : Set} → {n   : ℕ} → Vec (A → B) n → Vec A n → Vec B n
  multiapply {n = zero }       _        _  = []
  multiapply {n = suc _} (f ∷ fs) (a ∷ as) = f a ∷ multiapply fs as

  transpose  : {A   : Set} → {n m : ℕ} → Matrix A n m → Matrix A m n
  transpose  empty      = empty
  transpose (full list) = full (transpose' list)
    where
      transpose' : {A : Set} → {n m : ℕ} → Vec (Vec A m) n → Vec (Vec A n) m
      transpose'      []  = replicate []
      transpose' (l ∷ ls) = multiapply (multiapply (replicate _∷_) l) (transpose' ls)