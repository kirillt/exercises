module Universes where

  module Boolean where

    open import Data.Bool hiding (not)
  
    data   False : Set where
    record True  : Set where

    isTrue : Bool → Set
    isTrue true = True
    isTrue _    = False

    infixr 25 _and_

    not : Bool → Bool
    not true = false
    not _    = true

    _and_ : Bool → Bool → Bool
    true and true = true
    _    and _    = false

    not∘not≡id : (x : Bool) → isTrue (not (not x)) → isTrue x
    not∘not≡id true p = p
    not∘not≡id false ()

    intro-and : (x y : Bool) → isTrue x → isTrue y → isTrue (x and y)
    intro-and true  true  _  p = p
    intro-and _     false _ ()
    intro-and false _     () _

    open import Data.Nat

    not-zero : ℕ → Bool
    not-zero  zero   = false
    not-zero (suc _) = true

    _pseudo-div_ : ℕ → (x : ℕ) → {p : isTrue (not-zero x)} → ℕ
    a pseudo-div b = zero

  module Generics where

    data Functor : Set₁ where
      |Id|  : Functor
      |K|   : Set → Functor
      _|+|_ : Functor → Functor → Functor
      _|×|_ : Functor → Functor → Functor

    data _⊕_ (A B : Set) : Set where
      inl : A → A ⊕ B
      inr : B → A ⊕ B

    data _⊗_ (A B : Set) : Set where
      _,_ : A → B → A ⊗ B

    infixr 50 _|+|_ _⊕_
    infixr 60 _|×|_ _⊗_

    [_] : Functor → Set → Set
    [  |Id|   ] X = X
    [   |K| A ] X = A
    [ F |+| G ] X = [ F ] X ⊕ [ G ] X
    [ F |×| G ] X = [ F ] X ⊗ [ G ] X

    map : (F : Functor) → {X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
    map   |Id|    f x       = f x
    map (  |K| A) f c       = c
    map (F |+| G) f (inl l) = inl (map F f l)
    map (F |+| G) f (inr r) = inr (map G f r)
    map (F |×| G) f (l , r) = map F f l , map G f r

    data Fix (F : Functor) : Set where
      <_> : [ F ] (Fix F) → Fix F

    mapFold : {X : Set} → (F G : Functor) → ([ G ] → X) → [ F ] (Fix G) → [ F ] X
      
    fold : (F : Functor) → {A : Set} → ([ F ] A → A) → Fix F → A
    fold F f < x > = f (map F (fold F f) x)