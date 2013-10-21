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

Lemma equal_reverses_have_equal_lengths :
  forall xs ys : natlist, reverse xs = reverse ys -> length xs = length ys.
Proof.
  intros xs ys R.
  rewrite reverse_preserves_length.
  replace (length ys) with (length (reverse ys)).
  rewrite R.
  reflexivity.
  rewrite <- reverse_preserves_length.
  reflexivity.
Qed.

Lemma snoc_increases_length :
  forall (x : nat) (xs : natlist), length (snoc x xs) = S (length xs).
Proof.
  intros x xs.
  induction xs as [ | x' xs' ].
    reflexivity.
    simpl; rewrite IHxs'; reflexivity.
Qed.
      
Lemma snoc_injective :
  forall (x y : nat) (xs ys : natlist), snoc x xs = snoc y ys -> x :: xs = y :: ys.
Proof.
  intros x y xs.
  induction xs as [ | x' xs' ].
    intros ys.
    induction ys as [ | y' ys' ].
      intros eq; simpl in eq. apply eq.
      intros eq; simpl in eq; apply f_equal with (f := length) in eq; simpl in eq; rewrite snoc_increases_length in eq; discriminate.
    induction ys as [ | y' ys' ].
      intros eq; simpl in eq; apply f_equal with (f := length) in eq; simpl in eq; rewrite snoc_increases_length in eq; discriminate.
      intros eq; simpl in eq; inversion eq; apply IHxs' in H1; inversion H1; reflexivity.
Qed.
      
Theorem reverse_injective :
  forall xs ys : natlist, reverse xs = reverse ys -> xs = ys.
Proof.
  intro xs.
  induction xs as [ | x xs' ].
    intros ys.
    destruct ys as [ | y ys' ].
      reflexivity.
      intro R; apply equal_reverses_have_equal_lengths in R; discriminate.
    induction ys as [ | y ys' ].
      intro R; apply equal_reverses_have_equal_lengths in R; discriminate.
      intro R; simpl in R; apply snoc_injective in R; inversion R; apply IHxs' in H1; rewrite H1; reflexivity.
Qed.

(* Sergey Sinchuk's version *)

