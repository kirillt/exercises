Theorem plus_n_n_injective :
  forall n m : nat, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n; induction m.
    reflexivity.
    discriminate.
    discriminate.
    assert (T : forall a b : nat, S (a + b) = a + S b).
      induction a.
        reflexivity.
        simpl. intro b. rewrite IHa. reflexivity.
    intro eq. simpl in eq. rewrite <- T in eq. rewrite <- T in eq. inversion eq.
    apply IHn in H0.
    rewrite H0.
    reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective :
  forall n m : nat, double n = double m -> n = m.
Proof.
  intros n.
  induction n.
    intros m.
    induction m.
      reflexivity.
      discriminate.
    induction m.
      discriminate.
      intros eq.
      simpl in eq.
      inversion eq.
      apply IHn in H0.
      rewrite H0.
      reflexivity.
Qed.