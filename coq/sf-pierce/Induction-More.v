Require Export Basics.

Theorem ble_nat_refl :
  forall n : nat, true = ble_nat n n.
Proof.
  intro n.
  induction n.
    reflexivity.
    simpl; rewrite IHn; reflexivity.
Qed.

Theorem zero_beq_nat_S :
  forall n : nat, beq_nat 0 (S n) = false.
Proof.
  intro n.
  simpl; reflexivity.
Qed.

Theorem andb_false_r :
  forall b : bool, andb b false = false.
Proof.
  intro b.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem plus_ble_nat_compat_l :
  forall n m p : nat, ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intro  X.
  induction p.
    simpl; rewrite X; reflexivity.
    simpl; rewrite IHp; reflexivity.
Qed.

Theorem S_beq_nat_0 :
  forall n : nat, beq_nat (S n) 0 = false.
Proof.
  intro n.
  simpl; reflexivity.
Qed.

Theorem mult_left_unit :
  forall n : nat, 1 * n = n.
Proof.
  intro n.
  simpl. induction n.
    reflexivity.
    simpl; rewrite IHn; reflexivity.
Qed.

Theorem all3_spec :
  forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b.
    simpl. destruct c; reflexivity.
    reflexivity.
Qed.

Lemma plus_assoc :
  forall n m p : nat, n + (m + p) = n + m + p.
Proof.
  intros n m p.
  induction n.
    reflexivity.
    simpl; rewrite IHn; reflexivity.
Qed.
    
Theorem mult_plus_distr_right :
  forall n m p : nat, (n + m) * p = n * p + m * p.
Proof.
  intros n m p.
  induction n.
    reflexivity.
    simpl; rewrite IHn; rewrite plus_assoc; reflexivity.
Qed.

Lemma plus_comm :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
    induction m.
      reflexivity.
      simpl; rewrite <- IHm; reflexivity.
    assert (T : forall x y : nat, S (x + y) = x + S y).
      intros x y.
      induction x.
        reflexivity.
        simpl; rewrite <- IHx; reflexivity.
    simpl. rewrite IHn. rewrite T. reflexivity.
Qed.

Theorem mult_plus_distr_left :
  forall n m p : nat, n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n.
    reflexivity.
    simpl; rewrite IHn;
    rewrite plus_assoc;
    rewrite plus_assoc.
    assert (P : p + n * m = n * m + p).
      rewrite plus_comm; reflexivity.
    assert (M : m + p + n * m = m + (p + n * m)).
      rewrite plus_assoc; reflexivity.
    rewrite M.
    rewrite P.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc :
  forall n m p : nat, n * (m * p) = n * m * p.
Proof.
  intros n m p.
  induction n.
    reflexivity.
    simpl. rewrite IHn. rewrite mult_plus_distr_right. reflexivity.
Qed.

Theorem beq_nat_refl :
  forall n : nat, true = beq_nat n n.
Proof.
  intro n.
  induction n.
    reflexivity.
    simpl; rewrite IHn; reflexivity.
Qed.

Theorem plus_swap' :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  replace (n + m) with (m + n).
  rewrite plus_assoc.
  reflexivity.

  induction m.
    induction n.
      reflexivity.
      simpl; rewrite <- IHn; simpl; reflexivity.
    simpl; rewrite IHm.
    assert (T : forall x y : nat, S (x + y) = x + S y).
      intros x y.
      induction x.
        simpl; reflexivity.
        simpl; rewrite IHx; simpl; reflexivity.
    rewrite T.
    reflexivity.
Qed.