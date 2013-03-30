module Draft01

  Value : Type
  Value = Nat

  Variable : Type
  Variable = Nat

  record Binding : Type where
    KV : (key : Variable) ->
         (value : Value) ->
             Binding

  State : Type
  State = List Binding

  bind : Binding -> State -> State
  bind  kv [] = kv :: []
  bind (KV k v)  (KV k' v' :: ts)
    with (k == k')
      | True  =  KV k  v  :: ts
      | False =  KV k' v' :: (bind (KV k v) ts)

  fetch : Variable -> State -> Value
  fetch _ [] = 0
  fetch k (KV k' v' :: ts)
    with (k == k')
      | True  = v'
      | False = fetch k ts

  data A : Type where
    consta: Value -> A
    plus  : A -> A -> A
    star  : A -> A -> A
    var   : Variable -> A

  calc : State -> A -> Value
  calc s (consta x   ) = x
  calc s (plus   x y ) = (calc s x) + (calc s y)
  calc s (star   x y ) = (calc s x) * (calc s y)
  calc s (var    x   ) = fetch x s
   
  data B : Type where
    constb: Bool -> B
    conj  : B -> B -> B
    neg   : B -> B
    le    : A -> A -> B
    eq    : A -> A -> B

  isTrue : Bool -> Type
  isTrue true = ()

  isFalse : Bool -> Type
  isFalse false = ()

  cond : State -> B -> Bool
  cond s (constb x  ) = x
  cond s (conj   x y) = (cond s x) && (cond s y)
  cond s (neg    x  ) =           not (cond s x)
  cond s (le     x y) = (calc s x) <  (calc s y)
  cond s (eq     x y) = (calc s x) == (calc s y)
    
  data ST : Type where
    skip  : ST
    comp  : ST -> ST -> ST
    as    : Variable -> Value -> ST
    branch: B -> ST -> ST -> ST
    while : B -> ST -> ST

  data Transition : State -> State -> ST -> Type where
    TSkip : {s       :State} -> Transition s s skip
    TAs   : {s       :State} -> {k:Variable} -> {v:Value} -> Transition s (bind (KV k v) s) (as k v)
    TComp : {s1,s2,s3:State} -> {o1,o2:ST} -> Transition s1 s2 o1 -> Transition s2 s3 o2 -> Transition s1 s3 (comp o1 o2)

    TIf_t : {s1,s2   :State} -> {o1,o2:ST} -> {b:B} -> isTrue  (cond s1 b) ->
                   Transition s1 s2 o1 -> Transition s1 s2 (branch b o1 o2)
    TIf_f : {s1,s2   :State} -> {o1,o2:ST} -> {b:B} -> isFalse (cond s1 b) ->
                   Transition s1 s2 o2 -> Transition s1 s2 (branch b o1 o2)
    TWl_t : {s1,s2   :State} -> {o    :ST} -> {b:B} -> isTrue  (cond s1 b) ->
                   Transition s1 s2 o -> Transition s1 s2 (while b o)
    TWl_f : {s       :State} -> {o    :ST} -> {b:B} -> isFalse (cond s  b) ->
                   Transition s s (while b o)

  record Interpretation : State -> ST -> Type where
    I : (state : State) ->
        (transition : Transition s state p) ->
            Interpretation s p

  interpret : (p : ST) -> (s : State) -> Interpretation s p
  
--  interpret skip s = result s [skip]
  interpret skip s = ?skip

--  interpret (comp y₁ y₂) s₁ with interpret y₁ s₁
--  ... | result s₂ tr₁ with interpret y₂ s₂
--  ...     | result s₃ tr₂ = result s₃ ([comp] tr₁ tr₂)

--  interpret (comp y₁ y₂) s₁ = (state (interpret y₂ (state (interpret y₁ s₁)))) ,
--                                ([comp]
--                                    (transition (interpret y₁ s₁))
--                                    (transition (interpret y₂ (state (interpret y₁ s₁)))))

  interpret (comp y1 y2) s1 = ?comp
  
--  interpret (as k v) s = result ((k , v) |> s) [as]
  interpret (as k v) s = ?as
  
  interpret (branch b o1 o2) s = if cond s b then ?brt else ?brf
  
  interpret (while b o) s = if cond s b then ?wlt else ?wlf
