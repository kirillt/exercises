Theorem plus_left_neutral :
  forall n : nat, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_right_neutral :
  forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem minus_diag :
  forall n : nat, n - n = 0.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem mult_left_zero :
  forall n : nat, 0 * n = 0.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem mult_right_zero :
  forall n : nat, n * 0 = 0.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem plus_n_sm :
  forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  simpl; reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem plus_comm :
  forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
  simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
  simpl. induction m. rewrite IHn. reflexivity. rewrite IHn. rewrite plus_n_sm. reflexivity.
Qed.

Theorem plus_assoc :
  forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  simpl; reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall n, double n = n + n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl; rewrite IHn; rewrite plus_n_sm; reflexivity.
Qed.