Inductive binary : Type :=
  | Zero  : binary
  | Succ  : binary -> binary
  | Twice : binary -> binary.

Definition inc (b : binary) : binary :=
  match b with
  | Zero            => Succ Zero
  | Succ Zero       => Twice (Succ  Zero)
  | Succ (Succ  b') => Succ  (Twice (Succ  b'))
  | Succ (Twice b') => Twice (Succ  b')
  | Twice b'        => Succ  (Twice b')
  end.

Fixpoint toUnary (b : binary) : nat :=
  match b with
  | Zero     => O
  | Succ  b' => 1 + (toUnary b')
  | Twice b' => 2 * (toUnary b')
  end.

Fixpoint fromUnary (n : nat) : binary :=
  match n with
  | O    => Zero
  | S n' => inc (fromUnary n')
  end.

Theorem toUnary_is_fromUnary_inverse :
  forall n : nat, toUnary (fromUnary n) = n.
  
Theorem fromUnary_is_toUnary_inverse :
  forall b : binary, fromUnary (toUnary b) = b.
