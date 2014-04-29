Require Import Peano Le Compare.

Open Scope type_scope.

Class comparable A := {
  le     : A -> A -> Prop;
  le_dec : forall (l r : A), {le l r} + {le r l}
}.

Instance nat_comparable : comparable nat := {
  le := Peano.le; le_dec := Compare.le_dec
}.

Fixpoint insert {A} {p : comparable A} (x : A) (xs : list A) : list A :=
  match xs with
  | cons x' xs' =>
    match le_dec x x' with
    | left  _ => cons x xs
    | right _ => cons x' (insert x xs')
    end
  | nil => cons x nil
  end.

Fixpoint merge {A} {p : comparable A} (ls rs : list A) : list A :=
  match (ls, rs) with
  | (cons l ls', cons r rs') =>
    let (x,y) := match le_dec l r with
                 | left  _ => (l,r)
                 | right _ => (r,l)
                 end
    in cons x (cons y (merge ls' rs'))
  | (cons l ls', nil) => ls
  | (nil, cons r rs') => rs
  | (nil,nil) => nil
  end.

Fixpoint split {A} {p : comparable A} (xs : list A) : list A * list A :=
  match xs with
  | cons l (cons r xs') =>
    let (ls,rs) := split xs'
    in (cons l ls, cons r rs)
  | cons x xs' => (cons x nil, nil)
  | nil => (nil, nil)
  end.

Eval cbv in split (cons 1 (cons 2 (cons 3 nil))).

(*
Fixpoint merge_sort {A} {p : comparable A} (xs : list A) : list A :=
  if le_dec 2 (length xs)
  then let (ls,rs) := split xs
       in merge (merge_sort ls) (merge_sort rs)
  else xs.
*)

Definition length_order {A} (ls rs : list A) :=
  length ls < length rs.

Lemma le_eq {n m : nat} (P : n = m) : n <= m.
  rewrite P; exact (le_n m).
Qed.

Theorem length_order_wf' {A} (n : nat) : forall (xs : list A), length xs <= n -> Acc length_order xs.
  induction n; [
    intros xs H; inversion H; destruct xs; inversion H1;
    refine (Acc_intro _ _); intros y H2; inversion H2 |
    intros xs H; destruct xs; [
      refine (Acc_intro _ _); intros y H'; inversion H' |
      inversion H; [
        remember (IHn xs (le_eq H1)) as H2; clear HeqH2; refine (Acc_intro _ _);
        intros y L; inversion L as [H3|k H3 H4]; rewrite H1 in H3;
        [ apply le_eq in H3 | apply le_Sn_le in H3 ];
        exact (IHn y H3) | exact (IHn (cons a xs) H1) ] ] ].
Qed.

Theorem length_order_wf  {A} : well_founded (@length_order A).
  cbv [well_founded]; intro xs; remember (length xs) as n;
  exact (length_order_wf' n xs (le_eq (eq_sym Heqn))).
Qed.

Definition merge_sort {A} {p : comparable A} : list A -> list A.
  refine (Fix length_order_wf (fun _ => (list A))
              (fun xs (call : forall ys, length_order ys xs -> list A)
               => if le_dec 2 (length xs)
                  then let yss := split xs
                       in merge (call (fst yss) _) (call (snd yss) _)
                  else xs));
  cbv [length_order yss]; admit.
Qed.