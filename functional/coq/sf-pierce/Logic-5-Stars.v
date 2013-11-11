(* Filter and subsequences *)

Notation "[]" := nil.
Notation "h :: t" := (cons h t).
Notation "[ x ]" := (cons x nil).

Fixpoint filter {X} (p : X -> bool) (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' => if p x then x :: (filter p xs') else (filter p xs')
  end.

Inductive subsequence {X} : list X -> list X -> Prop :=
  | s_middle : forall (xl xm xr : list X), subsequence xm (xl ++ xm ++ xr)
  | s_insert : forall (xl xr s : list X) (m : X), subsequence s (xl ++ xr) -> subsequence s (xl ++ [m] ++ xr).

Inductive all {X} (p : X -> bool) : list X -> Prop :=
  | a_nil  : all p []
  | a_cons :forall (x : X) (xs : list X), all p xs -> p x = true -> all p (x :: xs).

Lemma filter_all {X} (p : X -> bool) (xs : list X) : all p (filter p xs).
Proof.
  induction xs.
    apply a_nil.
    assert (PA : {p a = true} + {p a = false}). destruct (p a). apply left; reflexivity. apply right; reflexivity.
    simpl; inversion PA.
      rewrite H; apply a_cons. apply IHxs. apply H.
      rewrite H; simpl; apply IHxs.
Qed.

Theorem filter_subseq {X} (p : X -> bool) :
  forall (xs s s' : list X), subsequence s xs -> all p s -> (filter p xs = s' <-> subsequence s' xs /\ all p s' /\ length s' >= length s).
Proof.
  intros xs s s' S AS.
  split.
    intros F.
      split.
(* TODO Emacs' undo is really strange :( *)
