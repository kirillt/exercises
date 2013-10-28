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
  forall x, (appears_in x xs -> ~ appears_in x ys) /\ (appears_in x ys -> ~ appears_in x xs).
