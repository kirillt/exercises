Require Import Arith.

Definition Value := nat.
Definition Name  := nat.

Record Binding : Set := KV
  {key   : Name;
   value : Value}.

Require Import List.

Definition State := list Binding.

Fixpoint bind (b : Binding) (s : State) :=
  match s with
  |     nil => b :: nil
  | h :: ts => match beq_nat (key b) (key h) with
               | true  => b :: ts
               | false => h :: (bind b ts)
               end
  end.

Fixpoint fetch (k : Name) (s : State) :=
  match s with
  |     nil => 0
  | h :: ts => match beq_nat k (key h) with
               | true  => value h
               | false => fetch k ts
               end
  end.

Inductive A : Set :=
  | consta: Value -> A
  | plus  : A -> A -> A
  | star  : A -> A -> A
  | var   : Name -> A.

Fixpoint calc (s : State) (a : A) :=
  match a with
  | consta x   => x
  | plus   x y => (calc s x) + (calc s y)
  | star   x y => (calc s x) * (calc s y)
  | var    x   => fetch x s
  end.

Inductive B : Set :=
  | constb: bool -> B
  | conj  : B -> B -> B
  | neg   : B -> B
  | le    : A -> A -> B
  | eq    : A -> A -> B.

Require Import Bool.

Require Import Compare_dec.

Fixpoint cond (s : State) (b : B) :=
  match b with
  | constb x   => x
  | conj   x y => (cond s x) && (cond s y)
  | neg    x   => negb (cond s x)
  | le     x y => leb     (calc s x) (calc s y)
  | eq     x y => beq_nat (calc s x) (calc s y)
  end.

Inductive ST : Set :=
  | skip  : ST
  | comp  : ST -> ST -> ST
  | assign: Name -> Value -> ST
  | branch: B -> ST -> ST -> ST
  | while : B -> ST -> ST.

Definition isTrue  (b : bool) := if b then True  else False. 
Definition isFalse (b : bool) := if b then False else True.

Record Control : Set := C
  {state   : State;
   program : option ST}.

Inductive Transition (s1 : State) : ST -> Control -> Set :=
  | TSkip  : Transition s1 skip (C s1 None)
  | TAssign: forall {k : Name} {v : Value}, Transition s1 (assign k v) (C (bind (KV k v) s1) None)
  | TComp_n: forall {s2 : State} {o1 o2    : ST},
               Transition s1 o1 (C s2 None) -> Transition s1 (comp o1 o2) (C s2 None)
  | TComp_s: forall {s2 : State} {o1 o2 o3 : ST},
               Transition s1 o1 (C s2 (Some o3)) -> Transition s1 (comp o1 o2) (C s2 (Some (comp o3 o2)))
  | TIf_t  : forall {s2 : State} {o1 o2 : ST} {b : B},
               isTrue  (cond s1 b) -> Transition s1 (branch b o1 o2) (C s1 (Some o1))
  | TIf_f  : forall {s2 : State} {o1 o2 : ST} {b : B},
               isFalse (cond s1 b) -> Transition s1 (branch b o1 o2) (C s1 (Some o2)).

Record Interpretation (s : State) (p : ST) : Set := I
  {control    : Control;
   transition : Transition s p control}.

Require Import CpdtTactics.

Definition final (s : State) : Control := C s None.

Definition interpret (p : ST) (s : State) : Interpretation s p.
Proof.

  
(*
  induction p.
  crush' final fail.
  crush' TSkip fail.
  crush' (I s skip i) fail.
  induction IHp1.
  induction control0.
  induction program0.
  Check TComp_s.
  Check TComp_s s.
  crush' (I s (comp p1 p2) (C state0 (Some (comp a p2))) (TComp_s s transition0)) fail.

  match p with
  | skip => I s skip (C s None) (TSkip s)
  end.
*)