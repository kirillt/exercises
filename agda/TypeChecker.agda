module TypeChecker where

  infixr 30 _⇒_
  data Type : Set where
    ₁   : Type
    _⇒_ : Type → Type → Type

  data Equal? : Type → Type → Set where
    yes : {t   : Type} → Equal? t t
    no  : {t s : Type} → Equal? s t

  _=?=_ : (s t : Type) → Equal? s t
  ₁ =?= ₁       = yes
  ₁ =?= (_ ⇒ _) = no
  (_ ⇒ _) =?= ₁ = no
  (a ⇒ b) =?= (x  ⇒  y) with a =?= x | b =?= y
  (a ⇒ b) =?= (.a ⇒ .b) | yes | yes = yes
  (a ⇒ b) =?= (x  ⇒  y) | _   | _   = no

  open import Data.Nat
  
  data Raw : Set where
    var : ℕ → Raw
    _$_ : Raw → Raw → Raw
    lam : Type → Raw → Raw
  
  open import Data.List
  
  Context = List Type

    module In where
    
      data _∈_ {A : Set} (x : A) : List A → Set where
          hd : {xs : List A} → x ∈ xs
          tl : {ys : List A} → x ∈ ys → {y : A} → x ∈ (y ∷ ys)

      index : {A : Set} → {xs : List A} → {x : A} → x ∈ xs → ℕ
      index  hd       = zero
      index (tl rest) = suc (index rest)

      data Lookup {A : Set} (xs : List A) : ℕ → Set where
        inside  : (x : A) → (x∈xs : x ∈ xs) → Lookup xs (index x∈xs)
        outside : {n : ℕ} → Lookup xs (length xs + n)

      _!_ : {A : Set} → (xs : List A) → (i : ℕ) → Lookup xs i
      (    []) !      i  = outside
      (x ∷ xs) !      0  = inside x hd
      (x ∷ xs) ! suc i with xs ! i
      (x ∷ xs) ! suc .(index   proof) | inside  y proof = inside y (tl proof)
      (x ∷ xs) ! suc .(length xs + i) | outside {i}     = outside

  open In
      
  data Term (Γ : Context) : Type → Set where
    var : {t   : Type} → t ∈ Γ → Term Γ t
    _$_ : {a b : Type} → Term Γ (a ⇒ b) → Term Γ a → Term Γ b
    lam : {a b : Type} → Term (a ∷ Γ) b → Term Γ (a ⇒ b)

  erase : {Γ : Context} → {t : Type} → Term Γ t → Raw
  erase (var  t∈Γ) = var (index t∈Γ)
  erase (f    $  a) = (erase f) $ (erase a)
  erase (lam {t} x) = lam t (erase x)

  data Infer (Γ : Context) : Raw → Set where
    ok  : {t : Type} → {x : Term Γ t} → Infer Γ (erase x)
    bad : {e : Raw} → Infer Γ e

  infer : (Γ : Context) → (r : Raw) → Infer Γ r
  
  infer Γ (var i) with Γ ! i
  infer Γ (var .(index   t∈Γ)) | inside t t∈Γ = ok
  infer Γ (var .(length Γ + n)) | outside {n} = bad
  
  infer Γ (f $ a) with infer Γ f
  ... | bad = bad
  infer Γ (.(erase x) $ a) | ok {₁}     {x} = bad
  infer Γ (.(erase x) $ a) | ok {q ⇒ w} {x} with infer Γ a
  ... | bad = bad
  infer Γ (.(erase x) $ .(erase y)) | ok {q ⇒ w} {x} | ok { p} {y} with p =?= q
  infer Γ (.(erase x) $ .(erase y)) | ok {q ⇒ w} {x} | ok {.q} {y} | yes = ok
  ... | no  = bad
  
  infer Γ (lam t a) with infer (t ∷ Γ) a
  infer Γ (lam t .(erase b)) | ok {s} {b} = ok
  ... | bad = bad


  
  test = infer (₁ ⇒ ₁ ∷ []) (lam (₁ ⇒ ₁) (lam ₁ (var 1 $ (var 2 $ var 0))))