module Sublists where

  open import Data.List hiding (drop; filter)

  data _⊂_ {A : Set} : List A → List A → Set where
    stop : [] ⊂ []
    drop : {y : A} → {xs ys : List A} → xs ⊂ ys →      xs  ⊂ (y ∷ ys)
    step : {z : A} → {xs ys : List A} → xs ⊂ ys → (z ∷ xs) ⊂ (z ∷ ys)

  ⊂-refl  : {A : Set} → (xs : List A) → xs ⊂ xs
  ⊂-refl       []  = stop
  ⊂-refl  (h ∷ ts) = step (⊂-refl ts)

  ⊂-trans : {A : Set} → {xs ys zs : List A} → xs ⊂ ys → ys ⊂ zs → xs ⊂ zs
  ⊂-trans {_} {h ∷ _} {.h ∷ _} {.h ∷ _} (step xs-ys) (step ys-zs) = step (⊂-trans xs-ys ys-zs)
  ⊂-trans {_} {    _} { h ∷ _} {.h ∷ _} (drop xs-ys) (step ys-zs) = drop (⊂-trans xs-ys ys-zs)
  ⊂-trans {_} {    _} {     _} { h ∷ _}       xs-ys  (drop ys-zs) = drop (⊂-trans xs-ys ys-zs)
  ⊂-trans {_} {   []} {    []} {    []}  stop         stop        = stop
  ⊂-trans {_} {    _} { _ ∷ _} {    []}  _ ()
  ⊂-trans {_} {_ ∷ _} {    []} {     _}  () _

  data Sublist {A : Set} : List A → Set where
    <>   : Sublist []
    _::_ : {xs : List A} → (x : A) → Sublist xs → Sublist (x ∷ xs)
    skip : {xs : List A} → {x : A} → Sublist xs → Sublist (x ∷ xs)

  forget : {A : Set} → {xs : List A} → Sublist xs → List A
  forget       <>  = []
  forget (x :: xs) = x ∷ (forget xs)
  forget (skip xs) =      forget xs

  sublist→⊂ : {A : Set} → (xs : List A) → (s : Sublist xs) → forget s ⊂ xs
  sublist→⊂      []         <>  = stop
  sublist→⊂ (x ∷ xs) ( skip ys) = drop (sublist→⊂ xs ys)
  sublist→⊂ (x ∷ xs) (.x :: ys) = step (sublist→⊂ xs ys)

  open import Data.Bool

  filter : {A : Set} → (f : A → Bool) → (xs : List A) → Sublist xs
  filter _      [] = <>
  filter f (x ∷ xs) with f x
  ... | true  = x :: (filter f xs)
  ... | false = skip (filter f xs)

  complement : {A : Set} → {xs : List A} → Sublist xs → Sublist xs
  complement {_} {    []}         _  = <>
  complement {_} {x ∷ xs} ( skip ys) = x :: (complement ys)
  complement {_} {x ∷ xs} (.x :: ys) = skip (complement ys)

  open import Category.Monad

  sublists : {A : Set} → (xs : List A) → List (Sublist xs)
  sublists      []  = <> ∷ []
  sublists (x ∷ xs) = let open RawMonad Data.List.monad
                      in  sublists xs >>= λ s → skip s ∷ x :: s ∷ []