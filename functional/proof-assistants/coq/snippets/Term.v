Inductive term : Set :=
  | truth       : term
  | falsehood   : term
  | zero        : term
  | succ        : term -> term
  | pred        : term -> term
  | iszero      : term -> term
  | conditional : term -> term -> term -> term.

Section IncrementalDefinitionWithSets.
  Require Import Classical_sets.

  Variable T : Set.
  Variable true  : T.
  Variable false : T.
  Variable conditional : T -> T -> T -> T.
  Variable zero   : T.
  Variable succ   : T -> T.
  Variable pred   : T -> T.
  Variable iszero : T -> T.

  Definition Map (X Y : Set) (xs : Ensemble X) (f : X -> Y) (y : Y) : Prop :=
    exists (x : X), y = f x.
  Definition Cross (X Y : Set) (xs : Ensemble X) (ys : Ensemble Y) (z : X*Y) : Prop :=
    match z with
    | (x,y) => xs x /\ ys y
    end.

  Definition apply1 (f : T -> T)           (ts : Ensemble T) := Map T T ts f.
  Definition apply3 (f : T -> T -> T -> T) (ts : Ensemble T) :=
    Map (T*T*T) T (Cross (T*T) T (Cross T T ts ts) ts)
      (fun xyz => match xyz with (xy,z) => match xy with (x,y) => f x y z end end).
  
  Fixpoint terms (i : nat) : Ensemble T :=
    match i with
    | O   => Triple T true false zero
    | S i => let terms' := terms i in Union T
      (Triple T true false zero)
      (Union T
        (Union T (Union T (apply1 succ terms') (apply1 pred terms')) (apply1 iszero terms'))
        (apply3 conditional terms'))
    end.

  Definition is_term (t : T) := exists i : nat, In T (terms i) t.

  Example contains_iszero_zero : exists (i : nat), In T (terms i) (iszero zero).
    Proof.
      apply ex_intro with (x:=1); unfold terms.
      apply Union_intror; apply Union_introl; apply Union_intror;
      unfold apply1; unfold Map; unfold In.
      apply ex_intro with (x:=zero).
      reflexivity.
    Qed.

  (* 3.2.5 *)
  Theorem cumulative : forall (i : nat), Included T (terms i) (terms (S i)).
    Proof.
      unfold Included; unfold In; intros i x.
      induction i.
        unfold terms; intro H; apply Union_introl; apply H.
        intro H; simpl in H; inversion_clear H.
          simpl; apply Union_introl; apply H0.
          inversion_clear H0; inversion_clear H; inversion_clear H0; unfold apply1; unfold Map.
            inversion H; simpl;
              apply Union_intror; apply Union_introl; apply Union_introl; apply Union_introl;
                apply ex_intro with (x:=x0); apply H0.
            inversion H; simpl;
              apply Union_intror; apply Union_introl; apply Union_introl; apply Union_intror;
                apply ex_intro with (x:=x0); apply H0.
            inversion H; simpl;
              apply Union_intror; apply Union_introl; apply Union_intror;
                apply ex_intro with (x:=x0); reflexivity.
            apply Union_intror; apply Union_intror;
              apply ex_intro with (x:=x0); reflexivity.
     Qed.

  Definition base  (ts : Ensemble T) :=
    In T ts  true    /\ In T ts  false   /\ In T ts  zero.
  Definition step1 (ts : Ensemble T) := forall t : T, In T ts t ->
    In T ts (succ t) /\ In T ts (pred t) /\ In T ts (iszero t).
  Definition step2 (ts : Ensemble T) := forall t1 t2 t3 : T, In T ts t1 -> In T ts t2 -> In T ts t3 ->
    In T ts (conditional t1 t2 t3).
  Definition minimal (ts : Ensemble T) (p : Ensemble T -> Prop) :=
    forall ts' : Ensemble T, p ts' -> Included T ts ts'.
  Definition property (ts : Ensemble T) :=
    base ts /\ step1 ts /\ step2 ts.
  Definition terms' (ts : Ensemble T) :=
    property ts /\ minimal ts property.

  (* 3.2.6 *)
  Theorem equi_forward  : forall (t : T) (ts : Ensemble T), terms' ts -> In T ts t -> is_term t.
    Proof.
      admit.
    Qed.
  Theorem equi_backward : forall (t : T) (ts : Ensemble T), terms' ts -> is_term t -> In T ts t.
    Proof.
      admit.
    Qed.

End IncrementalDefinitionWithSets.
