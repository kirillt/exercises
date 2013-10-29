Notation "[]" := nil.
Notation "h :: t" := (cons h t).
Notation "[ x ]" := (cons x nil).

(* Filter of merge of two lists *)

Fixpoint filter {X} (p : X -> bool) (xs : list X) : list X :=
  match xs with
  | nil => nil
  | cons x xs' => if p x then cons x (filter p xs') else filter p xs'
  end.

Inductive merge {X} : list X -> list X -> list X -> Prop :=
  | m_nil   :                                                       merge       []        []        []
  | m_left  : forall (l : X) (ls rs xs : list X), merge ls rs xs -> merge (l :: ls)       rs  (l :: xs)
  | m_right : forall (r : X) (ls rs xs : list X), merge ls rs xs -> merge       ls  (r :: rs) (r :: xs).

Inductive all {X} (p : X -> bool) : list X -> Prop :=
  | a_nil  : all p []
  | a_cons : forall (x : X) (xs : list X), all p xs -> p x = true -> all p (x :: xs).

Require Export Coq.Program.Basics.

Lemma compose_negb_is_true {X} (p : X -> bool) :
  forall (x : X), compose negb p x = true -> p x = false.
Proof. intros x C; compute in C; destruct (p x). discriminate. reflexivity. Qed.

Theorem merge_filter {X} (p : X -> bool) :
  forall (ls rs xs : list X), all p ls -> all (compose negb p) rs -> merge ls rs xs -> filter p xs = ls.
Proof.
  intros ls.
  induction ls.
    intros rs; induction rs.
      intros xs AL AR M; inversion M; reflexivity.
      intros xs AL AR M; inversion M.
        simpl; rewrite IHrs; inversion AR; compute in H7; apply compose_negb_is_true in H7.
          rewrite H7; reflexivity. apply a_nil. apply H6. apply H3.
    intros rs; induction rs.
      intros xs AL AR M; inversion M.
        inversion AL; simpl; rewrite H7; rewrite IHls with (rs:=[]). reflexivity. apply H6. apply AR. apply H3.
      intros xs AL AR M; inversion M.      
        inversion AL; simpl; rewrite H7; rewrite IHls with (rs:=a0 :: rs). reflexivity. apply H6. apply AR. apply H3.
        inversion AR; simpl; apply compose_negb_is_true in H7; rewrite H7. apply IHrs. apply AL. apply H6. apply H3.
Qed.
        
(* No repeats and disjoint *)

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
(* TODO *) admit.

(* TODO pigeonhole principle *)

