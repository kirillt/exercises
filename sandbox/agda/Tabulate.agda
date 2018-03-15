module Tabulate where

  open import Data.Nat

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (suc n)
    fsuc  : {n : ℕ} → Fin n → Fin (suc n)

  open import Function
  open import Data.Vec hiding (tabulate)

  tabulate : {n : ℕ} → {A : Set} → (Fin n → A) → Vec A n
  tabulate {zero } _ = []
  tabulate {suc _} f = f fzero ∷ tabulate (f ∘ fsuc)

  _!_      : {n : ℕ} → {A : Set} → Vec A n → Fin n → A
  _!_      {zero }       _  ()
  _!_      {suc _} (x ∷ xs)  fzero   = x
  _!_      {suc _} (x ∷ xs) (fsuc n) = xs ! n

  open import Relation.Binary.PropositionalEquality hiding (cong)

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong {_} {_} {x} {.x} f refl = refl

  !∘tabulate≡id : {n : ℕ} → {i : Fin n} → {A : Set} → (f : Fin n → A) → tabulate f ! i ≡ f i
  !∘tabulate≡id {zero } {()}     _
  !∘tabulate≡id {suc n} {fzero } _ = refl
  !∘tabulate≡id {suc n} {fsuc k} _ = !∘tabulate≡id {n} {k} _

  tabulate∘!≡id : {n : ℕ} → {A : Set} → (xs : Vec A n) → tabulate (_!_ xs) ≡ xs
  tabulate∘!≡id {zero }      []  = refl
  tabulate∘!≡id {suc n} (h ∷ ts) = cong (λ ts' → h ∷ ts') (tabulate∘!≡id ts)