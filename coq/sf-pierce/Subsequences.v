Require Export List.
Require Export Coq.Lists.List.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).

Inductive subsequence1 {X} : list X -> list X -> Prop :=
  | equal  : forall xs ys : list X, xs = ys -> subsequence1 xs ys
  | remove : forall (x : X) (xl xr ys : list X), subsequence1 (xl ++ [x] ++ xr) ys -> subsequence1 (xl ++ xr) ys.

Inductive subsequence2 {X} : list X -> list X -> Prop :=
(*  | sublist : forall yl yr : list X, subsequence2 yl (yl ++ yr) (* with this rule some theorems would be very easy *) *)
  | empty   : forall ys : list X, subsequence2 [] ys
  | addl    : forall (y : X) (xs yl yr : list X), subsequence2 xs yr -> subsequence2 ([y] ++ xs) (yl ++ [y] ++ yr)
  | addr    : forall (y : X) (xs yl yr : list X), subsequence2 xs yl -> subsequence2 (xs ++ [y]) (yl ++ [y] ++ yr).

(* TODO seems to be wrong definitions, look at Logic-5-Stars for correct one (but SF talks about 3 constructors instead of 2) *)

Theorem equal_defs_l2r {X} :
  forall xs ys : list X, subsequence1 xs ys -> subsequence2 xs ys.
Proof.
(* TODO *) admit.
Qed.

Theorem equal_defs_r2l {X} :
  forall xs ys : list X, subsequence2 xs ys -> subsequence1 xs ys.
Proof.
(* TODO *) admit.
Qed.

Theorem subseq_refl1 {X} :
  forall xs : list X, subsequence1 xs xs.
Proof.
  intros xs.
  apply equal.
  reflexivity.
Qed.

Theorem subseq_refl2 {X} :
  forall xs : list X, subsequence2 xs xs.
Proof.
  intros xs.
  induction xs.
    apply empty.
    assert (C : a :: xs = [a] ++ xs). reflexivity. rewrite C.
    assert (N : subsequence2 ([a] ++ xs) ([a] ++ xs) = subsequence2 ([a] ++ xs) ([] ++ [a] ++ xs)). reflexivity. rewrite N.
    apply addl; apply IHxs.
Qed.

Theorem subseq_concat_l1 {X} :
  forall xs yl yr : list X, subsequence1 xs yl -> subsequence1 xs (yl ++ yr).
Proof.
  admit.
Qed.

Theorem subseq_concat_r1 {X} :
  forall xs yl yr : list X, subsequence1 xs yr -> subsequence1 xs (yl ++ yr).
Proof.
  admit.
Qed.

Lemma subseq_cons_l2 {X} :
  forall (x : X) (xs ys : list X), subsequence2 (x :: xs) ys -> subsequence2 xs ys.
Proof.
  intros x xs ys S.
  inversion S.
    admit. admit.
Qed.

Lemma subseq_cons_r2 {X} :
  forall (y : X) (xs ys : list X), subsequence2 xs ys -> subsequence2 xs (y :: ys).
Proof.
  intros y xs ys S.
  apply subseq_cons_l2 with (x:=y).
    assert (Y : y :: ys = [] ++ [y] ++ ys). reflexivity. rewrite Y.
    assert (Q : y :: xs = [y] ++ xs). reflexivity. rewrite Q.
    apply addl. apply S.
Qed.

Theorem subseq_concat_l2 {X} :
  forall xs yl yr : list X, subsequence2 xs yl -> subsequence2 xs (yl ++ yr).
Proof.
  intros xs yl yr S.
  induction yr.
    admit. admit.
Qed.

Theorem subseq_concat_r2 {X} :
  forall xs yl yr : list X, subsequence2 xs yr -> subsequence2 xs (yl ++ yr).
Proof.
  intros xs yl yr S.
  induction yl.
    simpl; apply S.
    assert (C : a :: yl = [] ++ [a] ++ yl). reflexivity. rewrite C; rewrite <- 2! app_assoc.
(* TODO *) admit.
Qed.

Theorem subseq_trans1 {X} :
  forall (xs ys zs : list X), subsequence1 xs ys -> subsequence1 ys zs -> subsequence1 xs zs.
Proof.
(* TODO *) admit.
Qed.

Theorem subseq_trans2 {X} :
  forall (xs ys zs : list X), subsequence2 xs ys -> subsequence2 ys zs -> subsequence2 xs zs.
Proof.
(* TODO *) admit.
Qed.
