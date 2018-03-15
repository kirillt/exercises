Require Import Term.

Inductive numeric : term -> Prop :=
  | nv_zero : numeric zero
  | nv_succ : forall t, numeric t -> numeric (succ t).

Inductive value : term -> Prop :=
  | v_true  : value truth
  | v_false : value falsehood
  | nv      : forall t, numeric t -> value t.

Inductive transition_ss : term -> term -> Prop :=
  | e_if         : forall t1 t1' t2 t3, transition_ss t1 t1' ->
                                        transition_ss (conditional t1  t2 t3)
                                                   (conditional t1' t2 t3)
  | e_iftrue     : forall t1 t2, transition_ss (conditional truth     t1 t2) t1
  | e_iffalse    : forall t1 t2, transition_ss (conditional falsehood t1 t2) t2
  | e_succ       : forall t1 t2, transition_ss t1 t2 -> transition_ss (succ   t1) (succ   t2)
  | e_pred       : forall t1 t2, transition_ss t1 t2 -> transition_ss (pred   t1) (pred   t2)
  | e_iszero     : forall t1 t2, transition_ss t1 t2 -> transition_ss (iszero t1) (iszero t2)
  | e_predzero   : transition_ss (pred   zero) zero
  | e_predsucc   : forall t, numeric t -> transition_ss (pred (succ t)) t
  | e_iszerozero : transition_ss (iszero zero) truth
  | e_iszerosucc : forall t, numeric t -> transition_ss (iszero (succ t)) falsehood.

Notation "t1 ---> t2" := (transition_ss t1 t2) (at level 60).

Inductive transition_ss' : term -> term -> Prop :=
  | id    : forall t       , transition_ss' t t
  | wrap  : forall t1 t2   , transition_ss t1 t2 -> transition_ss' t1 t2
  | chain : forall t1 t2 t3, transition_ss t1 t2 -> transition_ss t2 t3 -> transition_ss' t1 t3.

Notation "t1 --*> t2" := (transition_ss' t1 t2) (at level 60).

Section RelationExtractionTest.
  Add LoadPath "/home/kirillt/code/sandbox/relation-extraction".
  Declare ML Module "relation_extraction_plugin".
  Extraction Relation Fixpoint Relaxed transition_ss [1] with numeric [1].

  Check transition_ss1.
  Print transition_ss1.

  Eval compute in transition_ss1 (succ (pred zero)).
  Eval compute in transition_ss1 (pred (succ zero)).

  Eval compute in transition_ss1 (pred (succ (pred zero))).
  (* should be same as previous due e_pred rule, i.e. zero *)

  Fixpoint eval (i : nat) (t : term) : term :=
    match i with
    | S i => match transition_ss1 t with
             | Some t => eval i t
             | None => t
             end
    | O => t
    end.

  Eval compute in eval 1000 (conditional (iszero (pred (succ (pred zero)))) truth falsehood).
  (* :( *)
End RelationExtractionTest.

Ltac unfold_transition_ss :=
  match goal with
  | [ T : ?X ---> ?Y, H : ?Y = ?Z |- _ ] => rewrite    H in T; inversion T
  | [ T : ?X ---> ?Y, H : ?Z = ?Y |- _ ] => rewrite <- H in T; inversion T
  end.

Lemma iszero_codomain : forall t t', iszero t ---> t' -> value t' -> t' = truth \/ t' = falsehood.
Proof. intros t t' T V; inversion V. left; reflexivity. right; reflexivity.
       inversion H; unfold_transition_ss. Qed.
       
Lemma iszero_domain   : forall t t', iszero t ---> t' -> value t' -> numeric t.
Proof. intros t t' T V.
       assert (C : t' = truth \/ t' = falsehood) by exact (iszero_codomain t t' T V).
       inversion C; unfold_transition_ss. exact nv_zero. refine (nv_succ _ H1). Qed.
  
(* 3.5.14 *)
Theorem determinancy : (forall H, H \/ ~H) -> forall t t' t'', t ---> t' /\ t ---> t'' -> t' = t''.
Proof.
  Ltac work :=
    repeat match goal with
    | [ A : ?X = ?Z, B : ?Y = ?Z |- _ ] => rewrite <- B in A; inversion A
    | [ A : ?X = ?Q, B : ?Y = ?W, C : ?X = ?Y |- _ ] =>
      rewrite A in C; rewrite B in C; apply C
    end.
  Ltac filter :=
    match goal with
    | [ A : numeric truth     |- _ ] => inversion A
    | [ A : numeric falsehood |- _ ] => inversion A
    | [ A : _ |- _ ] => idtac
    end.
  intro ex_middle; induction t; intros t' t'' H; inversion_clear H.
    destruct t'; destruct t''; try reflexivity; inversion H0.
    destruct t'; destruct t''; try reflexivity; inversion H0.
    destruct t'; destruct t''; try reflexivity; inversion H0.
    destruct t'; destruct t''; inversion H0; inversion H1;
      assert (t' = t'') by apply (IHt t' t'' (conj H3 H6));
      rewrite H7; reflexivity.
    destruct t'; destruct t''; inversion H0; inversion H1; try reflexivity; work; filter; admit.
    admit.
    admit.
Qed.

Inductive transition_ns : term -> term -> Prop :=
  | b_id         : forall v, value v -> transition_ns v v
  | b_iftrue     : forall t1 t2 v, value v -> transition_ns t1 v ->
                   transition_ns (conditional truth     t1 t2) v
  | b_iffalse    : forall t1 t2 v, value v -> transition_ns t2 v ->
                   transition_ns (conditional falsehood t1 t2) v
  | b_succ       : forall t v, numeric v -> transition_ns t v -> transition_ns (succ t) (succ v)
  | b_predzero   : forall t  , transition_ns t zero -> transition_ns (pred t) zero
  | b_predsucc   : forall t v, numeric v -> transition_ns t v -> transition_ns (pred (succ t)) v
  | b_iszerozero : forall t  , transition_ns t zero -> transition_ns (iszero t) truth
  | b_iszerosucc : forall t v, numeric v -> transition_ns t (succ v) -> transition_ns (iszero t) falsehood.

Notation "t1 ===> t2" := (transition_ns t1 t2) (at level 60).

Theorem ss_equi_ns : forall t t', (t --*> t' /\ value t') <-> t ===> t'.
Proof.
  intros t t'; split.
    intro H; inversion H.
      inversion H1; inversion H0.
        rewrite <- H2; exact (b_id truth v_true).
        destruct t.
          exact (b_id truth v_true).