Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst (x : natprod) : nat :=
  match x with
  | (l,r) => l
  end.

Definition snd (x : natprod) : nat :=
  match x with
  | (l,r) => r
  end.

Theorem urjective_pairing' :
  forall n m : nat, (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing :
  forall n : natprod, n = (fst n, snd n).
Proof.
  intro n.
  destruct n.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "[]" := (nil).
Notation "h :: t" := (cons h t).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n c : nat) : natlist :=
  match c with
  | O => []
  | S c' => n :: (repeat n c')
  end.

Fixpoint length (ns : natlist) : nat :=
  match ns with
  | [] => O
  | h :: t => S (length t)
  end.

Fixpoint append (ls rs : natlist) : natlist :=
  match ls with
  | [] => rs
  | h :: t => h :: (append t rs)
  end.

Notation "ls ++ rs" := (append ls rs).

Definition hd (default : nat) (xs : natlist) : nat :=
  match xs with
  | [] => default
  | h :: t => h
  end.

Definition tl (xs : natlist) : natlist :=
  match xs with
  | [] => []
  | h :: t => t
  end.

Fixpoint alternate (ls rs : natlist) : natlist :=
  match ls with
  | [] => rs
  | l :: ls' => match rs with
                | [] => ls
                | r :: rs' => l :: r :: (alternate ls' rs')
                end
  end.

Example test_alternate1 : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]. Proof. reflexivity. Qed.
Example test_alternate2 : alternate [] [20;30] = [20;30].            Proof. reflexivity. Qed.
Example test_alternate3 : alternate [1] [4;5;6;7] = [1;4;5;6;7].     Proof. reflexivity. Qed.
Example test_alternate4 : alternate [1;2] [4;5;6;7] = [1;4;2;5;6;7]. Proof. reflexivity. Qed.

Theorem nil_is_left_zero :
  forall xs : natlist, [] ++ xs = xs.
Proof.
  intro xs.
  reflexivity.
Qed.

Theorem nil_is_right_zero :
  forall xs : natlist, xs ++ [] = xs.
Proof.
  intro xs.
  induction xs.
    reflexivity.
    simpl; rewrite IHxs; reflexivity.
Qed.

Theorem tl_length_pred :
  forall xs : natlist, pred (length xs) = length (tl xs).
Proof.
  intro xs.
  destruct xs;
    simpl; reflexivity.
Qed.

Theorem append_assoc :
  forall xs ys zs : natlist, (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
  intros xs ys zs.
  induction xs.
    reflexivity.
    simpl; rewrite IHxs; reflexivity.
Qed.

Theorem append_length :
  forall xs ys : natlist, length (xs ++ ys) = length xs + length ys.
Proof.
  intros xs ys.
  induction xs.
    reflexivity.
    simpl; rewrite IHxs; reflexivity.
Qed.

Fixpoint snoc (n : nat) (ns : natlist) : natlist :=
  match ns with
  | [] => [n]
  | h :: t => h :: (snoc n t)
  end.

Fixpoint reverse (ns : natlist) : natlist :=
  match ns with
  | [] => []
  | h :: t => snoc h (reverse t)
  end.

Theorem reverse_preserves_length :
  forall xs : natlist, length xs = length (reverse xs).
Proof.
  intro xs.
  induction xs.
    reflexivity.
    simpl.
    assert (L : forall a : nat, forall ns : natlist, length (snoc a ns) = S (length ns)).
      intros a ns.
      induction ns.
        reflexivity.
        simpl; rewrite IHns; reflexivity.
    rewrite L.
    rewrite IHxs.
    reflexivity.
Qed.