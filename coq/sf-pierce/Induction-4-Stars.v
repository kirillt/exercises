Theorem plus_swap :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (C : forall a b,   a + b = b + a).
    intros a b.
    induction a.
      simpl; induction b; simpl.
        reflexivity.
        rewrite <- IHb. reflexivity.
      simpl. rewrite IHa. induction b.
        simpl; reflexivity.
        assert (P : forall x y : nat, S (x + y) = x + S y).
          intros x y.
          induction x.
            simpl; reflexivity.
            simpl; rewrite IHx; reflexivity.
        rewrite P; reflexivity.    
  assert (A : forall a b c, a + (b + c) = (a + b) + c).
    intros a b c.
    induction a.
      simpl; reflexivity.
      simpl; rewrite IHa; reflexivity.
  assert (C' : m + p = p + m).
    rewrite C; reflexivity.
  rewrite C'.
  rewrite A.
  rewrite C.
  reflexivity.
Qed.

Theorem mult_is_sum :
  forall n m : nat, n * S m = n + n * m.
Proof.
  intros n m.
  induction n.
    reflexivity.
    simpl. rewrite IHn. rewrite plus_swap. reflexivity.
Qed.

Theorem mult_commutes :
  forall n m : nat, n * m = m * n.
Proof.
  intros n m.
  induction n.
    simpl. induction m.
      reflexivity.
      simpl; rewrite <- IHm. reflexivity.
    simpl. rewrite mult_is_sum. rewrite IHn. reflexivity.
Qed.