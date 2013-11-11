Require Export List.
Require Export Coq.Lists.List.

Notation "[]" := nil.
Notation "h :: t" := (cons h t).
Notation "[ x ]" := (cons x nil).

(* TODO rather hard to prove with this definition, maybe existential lemma (subseq_parts) will help? *)

Inductive subsequence {X} : list X -> list X -> Prop :=
  | s_middle : forall (xl xm xr : list X), subsequence xm (xl ++ xm ++ xr)
  | s_insert : forall (xl xr s : list X) (m : X), subsequence s (xl ++ xr) -> subsequence s (xl ++ [m] ++ xr).

Theorem subseq_nil {X} :
  forall xs : list X, subsequence [] xs.
Proof.
  intros xs.
  assert (xs = xs ++ [] ++ []). rewrite <- app_nil_end; reflexivity.
  rewrite H.
  apply s_middle.
Qed.

Theorem subseq_refl {X} :
  forall xs : list X, subsequence xs xs.
Proof.
  intros xs.
  assert (xs = [] ++ xs ++ []). rewrite <- app_nil_end; reflexivity.
  assert (subsequence xs xs = subsequence xs ([] ++ xs ++ [])). rewrite <- H; reflexivity.
  rewrite H0.
  apply s_middle.
Qed.

Lemma subseq_parts {X} :
  forall (s xl xr : list X), (forall (a b : X), {a = b} + {a <> b}) -> subsequence s (xl ++ xr) ->
    (exists sl, exists sr, sl ++ sr = s /\ subsequence sl xl /\ subsequence sr xr).
Proof.
  intros s xl.
  generalize dependent s.
  induction xl.
    intros s xr eq S; apply ex_intro with (x:=[]). apply ex_intro with (x:=s).
      split.
        reflexivity.
        split.
          apply subseq_nil.
          simpl in S; apply S.
    intros s xr eq S; induction s.
      apply ex_intro with (x:=[]). apply ex_intro with (x:=[]).
        split.
          reflexivity.
          split; apply subseq_nil.
      destruct (eq a0 a).
  admit. admit.
Qed.
  
Lemma subseq_cons_l {X} :
  forall (x : X) (xs ys : list X), subsequence (x :: xs) ys -> subsequence xs ys.
Proof.
  intros x xs ys S.
  inversion S.
    assert (subsequence xs (xl ++ (x :: xs) ++ xr) = subsequence xs ((xl ++ [x]) ++ xs ++ xr)). rewrite <- app_assoc; reflexivity.
      rewrite H1; apply s_middle.
    admit. 
Qed.

Lemma subseq_cons_r {X} :
  forall (y : X) (xs ys : list X), subsequence xs ys -> subsequence xs (y :: ys).
Proof.
  admit.
Qed.

Theorem subseq_concat_l {X} :
  forall xs yl yr : list X, subsequence xs yl -> subsequence xs (yl ++ yr).
Proof.
  admit.
Qed.

Theorem subseq_concat_r {X} :
  forall xs yl yr : list X, subsequence xs yr -> subsequence xs (yl ++ yr).
Proof.
  admit.
Qed.

Theorem subseq_trans {X} :
  forall (xs ys zs : list X), subsequence xs ys -> subsequence ys zs -> subsequence xs zs.
Proof.
  admit.
Qed.
