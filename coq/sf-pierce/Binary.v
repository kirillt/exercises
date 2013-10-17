Inductive binary : Type :=
  | Zero  : binary
  | Succ  : binary -> binary
  | Twice : binary -> binary.

Definition inc (b : binary) : binary :=
  match b with
  | Zero            => Succ Zero
  | Succ Zero       => Twice (Succ  Zero)
  | Succ (Succ  b') => Succ  (Succ  (Succ  b'))
  | Succ (Twice b') => Twice (Succ  b')
  | Twice b'        => Succ  (Twice b')
  end.

Fixpoint toUnary (b : binary) : nat :=
  match b with
  | Zero     => O
  | Succ  b' => S (toUnary b')
  | Twice b' =>   (toUnary b') + (toUnary b')
  end.

Fixpoint fromUnary (n : nat) : binary :=
  match n with
  | O    => Zero
  | S n' => inc (fromUnary n')
  end.

Theorem toUnary_commutes_with_inc :
  forall b : binary, 1 + (toUnary b) = toUnary (inc b).
Proof.
  intro b.
  induction b.
    reflexivity.
    induction b.
      simpl; reflexivity.
      simpl; reflexivity.
      simpl. assert (T : forall x y : nat, S (x + y) = x + S y).
        intros x y.
        induction x.
          reflexivity.
          simpl; rewrite IHx; simpl; reflexivity.
      rewrite T.
      reflexivity.
    simpl; reflexivity.
Qed.
          
Theorem toUnary_is_fromUnary_inverse :
  forall n : nat, toUnary (fromUnary n) = n.
Proof.
  intro n.
  induction n.
    reflexivity.
    simpl; rewrite <- toUnary_commutes_with_inc; simpl; rewrite IHn; reflexivity.
Qed.