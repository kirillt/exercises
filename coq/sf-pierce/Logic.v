Theorem proj_left :
  forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q A.
  inversion A.
    apply H.
Qed.

Theorem proj_right :
  forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q A.
  inversion A.
    apply H0.
Qed.

Theorem and_comm :
  forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q A.
  inversion A.
    apply conj.
      apply H0.
      apply H.
Qed.

Theorem and_assoc :
  forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R A.
  inversion A; inversion H0.
  apply conj. apply conj.
  apply H. apply H1. apply H2.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q).

Theorem iff_sym :
  forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q I.
  inversion I.
  apply conj.
  apply H0.
  apply H.
Qed.

Theorem iff_refl :
  forall P : Prop, P <-> P.
Proof.
  intro P.
  apply conj;
    intro H; apply H.
Qed.

Theorem iff_trans :
  forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R PQ QR.
  inversion PQ; inversion QR.
  apply conj.
    intro HP; apply H  in HP; apply H1 in HP; apply HP.
    intro HR; apply H2 in HR; apply H0 in HR; apply HR.
Qed.

Theorem or_comm :
  forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q O.
  inversion O.
    right. apply H.
    left. apply H.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) -> (P \/ Q) \/ R.
Proof.
  intros P Q R O.
  inversion O.
    left; left; apply H.
    inversion H.
      left; right; apply H0.
      right; apply H0.
Qed.

Theorem or_distributes_over_and_forward :
  forall P Q R : Prop, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R O.
  inversion O.
    split.
      left; apply H.
      left; apply H.
    inversion H.
    split.
      right; apply H0.
      right; apply H1.
Qed.

Theorem or_distributes_over_and_backward :
  forall P Q R : Prop, (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R A.
  inversion A; inversion H; inversion H0.
    left; apply H1.
    left; apply H1.
    left; apply H2.
    right; split.
      apply H1.
      apply H2.
Qed.

Theorem or_distributes_over_and :
  forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split.
    apply or_distributes_over_and_forward.
    apply or_distributes_over_and_backward.
Qed.

Theorem anb_intro :
  forall b c, andb b c = true -> b = true /\ c = true.
Proof.
  intros b c A.
  split.
  destruct b.
    reflexivity.
    discriminate.
  destruct c.
    reflexivity.
    destruct b; discriminate.
Qed.

Theorem false_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intro F.
  inversion F.
Qed.

Theorem nonsense_implies_false :
  2 + 2 = 5 -> False.
Proof.
  intro F.
  inversion F.
Qed.

Theorem false_proves_any :
  forall P : Prop, False -> P.
Proof.
  intros P F.
  inversion F.
Qed.

Theorem not_false :
  ~ False.
Proof.
  unfold not. apply false_proves_any.
Qed.

Theorem contradiction_proves_any :
  forall P Q : Prop, (P /\ ~ P) -> Q.
Proof.
  intros P Q A.
  inversion A.
  unfold not in H0.
  apply false_proves_any.
  apply H0.
  apply H.
Qed.

Theorem double_neg :
  forall P : Prop, P -> ~ ~ P.
Proof.
  intros P H.
  unfold not.
  intros F.
  apply F.
  apply H.
Qed.

Theorem contrapositive :
  forall P Q : Prop, (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q PQ.
  unfold not.
  intros QF HP.
  apply QF.
  apply PQ.
  apply HP.
Qed.

Theorem not_both_true_and_false :
  forall P : Prop, ~ (P /\ ~ P).
Proof.
  unfold not.
  intros P C.
  inversion C.
    apply H0.
    apply H.
Qed.

(* Equivalent axioms for classical logic: *)

Definition pierce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop, ~ ~ P -> P.
Definition excluded_middle := forall P : Prop, P \/ ~ P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~ P \/ Q).

(* TODO: Prove it. *)

Theorem not_false_then_true :
  forall b : bool, b <> false -> b = true.
Proof.
  intros b bnf.
  unfold not in bnf.
  destruct b.
    reflexivity.
    apply false_proves_any.
    apply bnf. reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | _ => false
         end
  | S n' => match m with
         | S m' => beq_nat n' m'
         | _ => false
         end
  end.

Lemma sn_neq_sm_means_n_neq_m :
  forall n m, S n <> S m -> n <> m.
Proof.
  unfold not.
  intros n m NEQS NEQ.
  apply (f_equal) with (f:=S) in NEQ.
  apply NEQS in NEQ.
  apply NEQ.
Qed.

Theorem false_beq_nat :
  forall n m : nat, n <> m -> beq_nat n m = false.
Proof.
  intros n.
  induction n; destruct m.
    intros NNM; apply false_proves_any; apply NNM; reflexivity.
    reflexivity.
    reflexivity.
    intros NNM; simpl; apply sn_neq_sm_means_n_neq_m in NNM; apply IHn; apply NNM.
Qed.

Theorem beq_nat_false :
  forall n m, beq_nat n m = false -> n <> m.
Proof.
  unfold not.
  intros n.
  induction n; destruct m.
    discriminate.
    discriminate.
    discriminate.
    intros  NEQ H; simpl in NEQ; apply IHn in NEQ. apply NEQ. inversion H; reflexivity.
Qed.

Example exists_1 :
  exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (x:=2).
  reflexivity.
Qed.

Example exists_2 :
  forall n, (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n E.
  inversion E.
  apply ex_intro with (x:=2+x).
  simpl; simpl in H; apply H.
Qed.

Theorem forall_means_not_exists {X} :
  forall P : X -> Prop, (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros P F E.
  inversion E.
  apply H in F; apply F.
Qed.

Theorem not_exists_means_forall {X} :
  forall P : X -> Prop, excluded_middle -> ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros P M E x.
  unfold excluded_middle in M.
(* TODO *) admit.
Qed.

Theorem leibniz_equality :
  forall (X : Type) (x y : X), x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y E P F.
  rewrite <- E.
  apply F.
Qed.