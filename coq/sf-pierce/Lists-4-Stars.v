Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "[]" := (nil).
Notation "h :: t" := (cons h t).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (ns : natlist) : nat :=
  match ns with
  | [] => O
  | h :: t => S (length t)
  end.

Fixpoint snoc (n : nat) (ns : natlist) : natlist :=
  match ns with
  | [] => [n]
  | h :: t => h :: (snoc n t)
  end.

Fixpoint reverse (ns : natlist) : natlist :=
  match ns with
  | [] => []
  | h :: t => snoc h (reverse t)
  end.

Lemma snoc_gives_cons :
  forall x : nat, forall xs : natlist, exists y : nat, exists ys : natlist, snoc x xs = cons y ys.
Proof.
  intros x xs.
  destruct xs.
    exists x; exists []; reflexivity.
    exists n; exists (snoc x xs); simpl; reflexivity.
Qed.

Theorem reverse_preserves_length :
  forall xs : natlist, length xs = length (reverse xs).
Proof.
  intro xs.
  induction xs.
    reflexivity.
    simpl.
    assert (L : forall a : nat, forall ns : natlist, length (snoc a ns) = S (length ns)).
      intros a ns.
      induction ns.
        reflexivity.
        simpl; rewrite IHns; reflexivity.
    rewrite L.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem reverse_is_injective :
  forall xs ys : natlist, reverse xs = reverse ys -> xs = ys.
Proof.
  intros xs ys.
  intro R.
  assert (L : length xs = length ys).
    rewrite reverse_preserves_length.
    replace (length ys) with (length (reverse ys)).
    rewrite R.
    reflexivity.
    rewrite <- reverse_preserves_length.
    reflexivity.
(* possible way -- induction by length of lists *)
(*
  assert (W : forall n : nat, length xs = n -> length ys = n -> xs = ys).
    intro n.
    induction n as [ | n' ].
      induction xs as [ | x xs' ]; induction ys as [ | y ys' ]. reflexivity. discriminate. discriminate. discriminate.
      induction xs as [ | x xs' ]; induction ys as [ | y ys' ]. discriminate. discriminate. discriminate.
        simpl. admit.
  elim W with (length xs).
  reflexivity.
  reflexivity.
  rewrite L; reflexivity.
*)
  destruct xs as [ | x xs' ].
    destruct ys as [ | y ys' ].
      reflexivity.
      simpl in L. discriminate.
    destruct ys as [ | y ys' ].
      simpl in L. discriminate.
      assert (x = y).
        simpl in R.
(* ? *)