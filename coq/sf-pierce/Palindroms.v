Require Export List.
Require Export Coq.Lists.List.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).

Inductive palindrom {X} : list X -> Prop :=
  | empty  : palindrom nil
  | single : forall (x : X), palindrom [x]
  | append : forall (x : X) (m : list X), palindrom m -> palindrom ([x] ++ m ++ [x]).

Theorem palindrom_means_reverse_equal {X} :
  forall (xs : list X), palindrom xs -> rev xs = xs.
Proof.
  intros xs P.
  induction P.
    reflexivity.
    reflexivity.
    simpl; rewrite rev_app_distr; simpl; rewrite IHP; reflexivity.
Qed.

Theorem concat_reverse {X} :
  forall (xs : list X), palindrom (xs ++ rev xs).
Proof.
  intros xs.
  induction xs.
    simpl; apply empty.
    assert (H : [a] ++ xs = a :: xs). reflexivity.
    assert (R : rev ([a] ++ xs) = rev xs ++ [a]). reflexivity.
    assert (M: [a] ++ (xs ++ rev xs) ++ [a] = [a] ++ xs ++ rev xs ++ [a]). rewrite <- app_assoc; reflexivity.
    rewrite <- H; rewrite R; rewrite <- app_assoc; rewrite <- M; apply append; apply IHxs.    
Qed.

Theorem reverse_equal_means_palindrom {X} :
  forall (xs : list X), rev xs = xs -> palindrom xs.
Proof.
  intros xs R.
  induction xs.
    apply empty.
    simpl in R. induction (rev xs).
      simpl in R; inversion R; apply single.
    admit.
(* TODO *)
Qed.

(* TODO (just for fun) *)

Lemma reverse_middle {X} :
  forall (x : X) (m : list X), rev (x :: m ++ [x]) = x :: m ++ [x] -> rev m = m.
Proof.
  intros x xs R.
  admit.
Qed.

Fixpoint reverse_equal_means_palindrom {X} (xs : list X) (p : rev xs = xs) : palindrom xs :=
  match xs with
  | [] => empty
  | h :: t => match rev t with
              | [] => single
              | _ :: m => append h t (reverse_equal_means_palindrom m (reverse_middle h m h p))
              end
  end.
