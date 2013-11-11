Require Export List.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Plus.

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
  destruct xs as [ | h xs' ] _eqn:H.
    apply empty.
    induction (xs', rev xs') as ([ | h' xs'' ],[ | t m ]) _eqn:I.
      inversion I; simpl; apply single.
      inversion I; apply single.
      inversion I; simpl in H2.
        assert (HL : length (rev xs'' ++ [h']) = length (@nil X)). rewrite H2; reflexivity.
        rewrite app_length in HL; rewrite plus_comm in HL; simpl in HL; discriminate.
      inversion I; simpl in H2.
        assert (RM : rev m = m). admit.
        assert (RS : [h'] = rev [h']). reflexivity.
        rewrite <- RM in H2; rewrite <- rev_unit in H2; rewrite RS in H2; rewrite <- rev_app_distr in H2.
        assert (H3 : [h'] ++ xs'' = m ++ [t]). admit. (* reverse_injective proved in other module *)
        simpl in H3; rewrite H3.
Qed.

(* TODO (just for fun) *)

Fixpoint reverse_equal_means_palindrom {X} (xs : list X) (p : rev xs = xs) : palindrom xs :=
  match xs with
  | [] => empty
  | h :: t => match rev t with
              | [] => single
              | _ :: m => append h t (reverse_equal_means_palindrom m (reverse_middle h m h p))
              end
  end.
