(* TODO exercise with filter of merge of two lists (4 stars) *)
(* TODO exercise with filter and subsequences (5 stars) *)

Inductive appears_in {X} (x : X)  : list X -> Prop :=
  | ai_here  : forall xs, appears_in x (cons x xs)
  | ai_later : forall xs x', appears_in x xs -> appears_in x (cons x' xs).

Lemma appears_in_app {X} :
  forall (xs ys : list X) (x : X), appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros xs ys x A.
  induction xs.
    simpl in A; right; apply A.
    inversion A.
      left; apply ai_here.
      apply IHxs in H0.
      inversion H0.
        left; apply ai_later; apply H2.
        right; apply H2.
Qed.

Lemma app_appears_in {X} :
  forall (xs ys : list X) (x : X), appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros xs ys x O.
  induction xs.
    inversion O.
      inversion H.
      simpl; apply H.
    inversion O.
      inversion H.
        apply ai_here.
        apply ai_later; apply IHxs; left; apply H1.
      simpl; apply ai_later; apply IHxs; right; apply H.
Qed.

Definition disjoint {X} (xs ys : list X) : Prop :=
  forall x, (appears_in x xs -> ~ appears_in x ys).

Inductive appears_once {X} : X -> list X -> Prop :=
  ao : forall x (xl xr : list X), ~ appears_in x xl -> ~ appears_in x xr -> appears_once x (xl ++ (cons x nil) ++ xr).

Definition no_repeats {X} (xs : list X) : Prop :=
  forall x, appears_in x xs -> appears_once x xs.

Lemma double_appears_in {X} :
  forall (a x y : X) (xs ys : list X), appears_in a (x :: xs) -> appears_in a (y :: ys) -> ~ appears_once a ((x :: xs) ++ (y :: ys)).
Proof.
  unfold not.
  intros a x y xs ys AX AY AO.
  inversion AO.
    induction xl.
      simpl in H. inversion H.
        assert (appears_in a xr).
          rewrite H5; apply app_appears_in; right; apply AY.
        contradiction.
      admit.
Qed.
      
Theorem no_repeats_means_disjoint {X} :
  forall xs ys : list X, no_repeats (xs ++ ys) -> disjoint xs ys.
Proof.
  unfold disjoint.
  unfold no_repeats.
  intros xs ys N x AX AY.
  assert (appears_in x (xs ++ ys)).
    apply app_appears_in; left; apply AX.
  apply N in H.
  destruct xs; destruct ys.
    inversion AX. inversion AX. inversion AY.
    assert (~ appears_once x ((x0 :: xs) ++ (x1 :: ys))).
      apply double_appears_in. apply AX. apply AY.
    contradiction.
Qed.

Theorem disjoint_of_no_repeats_means_no_repeats {X} :
  forall xs ys : list X, no_repeats xs -> no_repeats ys -> disjoint xs ys -> no_repeats (xs ++ ys).
Proof.
  unfold disjoint.
  unfold no_repeats.
  intros xs ys AOX AOY D x AOXY.
  generalize dependent ys.
  induction xs.
    intros ys AOY D AXY.
    induction ys.
      inversion AXY.
      simpl in IHys; simpl in AXY; simpl. apply AOY in AXY. apply AXY.
    intros ys AOY D AXY.
(* TODO *)