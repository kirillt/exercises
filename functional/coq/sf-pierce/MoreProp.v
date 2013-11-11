Inductive total : nat -> nat -> Prop :=
  any : forall n m, total n m.

Inductive empty : nat -> nat -> Prop :=
  .

Inductive le : nat -> nat -> Prop :=
  | eq : forall n, le n n
  | su : forall n m, le n m -> le n (S m).

Lemma le_trans :
  forall a b c, le a b -> le b c -> le a c.
Proof.
  intros a b c LL LR.
  induction c.
    inversion LL; inversion LR. apply eq. rewrite <- H1 in H3; discriminate.
    inversion LR. rewrite <- H0; apply LL. apply su; apply IHc; apply H1.
Qed.

Theorem O_le_n :
  forall n, le 0 n.
Proof.
  intro n.
  induction n.
    apply eq.
    apply su; apply IHn.
Qed.

Theorem le_S :
  forall n m, le n m -> le (S n) (S m).
Proof.
  intros n m L.
  induction L.
    apply eq.
    apply su. apply IHL.
Qed.

Theorem le_S' :
  forall n m, le (S n) (S m) -> le n m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
    intros n L. destruct n. apply eq. inversion L. inversion H1.
    intros n L. inversion L. apply eq. apply su. apply IHm. apply H1.
Qed.

Theorem le_S'' :
  forall n m, le (S n) m -> le n m.
Proof.
  intros n m.
  generalize dependent n.
  destruct m.
    intros; inversion H.
    intros. apply le_S' in H; apply su in H; apply H.
Qed.

Require Export Coq.Arith.Plus.

Theorem le_plus_l :
  forall a b, le a (a + b).
Proof.
  intros a b.
  generalize dependent a.
  induction b.
    intro a; rewrite plus_comm; simpl; apply eq.
    intro a; rewrite plus_comm; simpl; apply su. rewrite plus_comm; apply IHb.
Qed.

Definition lt (n m : nat) := le (S n) m.
Notation "a < b" := (lt a b).

Lemma plus_le :
  forall a b, le a (a + b).
Proof.
  intros a b.
  rewrite plus_comm;
  induction b.
    simpl; apply eq.
    simpl; apply su. apply IHb.
Qed.

Theorem plus_lt :
  forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m L.
  unfold lt; unfold lt in L; inversion L.
    apply conj.
      apply le_S; apply plus_le.
      apply le_S; rewrite plus_comm; apply plus_le.
    apply conj.
      apply le_S. apply le_S'' in H. apply le_trans with (b:=n1 + n2).
        apply plus_le.
        apply H.
      apply le_S. apply le_S'' in H. apply le_trans with (b:=n1 + n2).
        rewrite plus_comm; apply plus_le.
        apply H.
Qed.

Theorem lt_S :
  forall n m, n < m -> n < S m.
Proof.
  intros n m L.
  apply su; apply L.
Qed.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => ble_nat n' m'
            end
  end.

Theorem ble_nat_to_le :
  forall n m, ble_nat n m = true -> le n m.
Proof.
  intros n.
  induction n.
    intros m B; apply O_le_n.
    intros m B. destruct m.
      discriminate.
      simpl in B; apply le_S; apply IHn. apply B.
Qed.

Theorem le_to_ble_nat :
  forall n m, le n m -> ble_nat n m = true.
Proof.
  intros n m;
  generalize dependent n.
  induction m.
    intros n L; inversion L; reflexivity.
    intros n L; induction n.
      reflexivity.
      simpl; apply le_S' in L; apply IHm. apply L.
Qed.

Theorem ble_nat_trans :
  forall a b c, ble_nat a b = true -> ble_nat b c = true -> ble_nat a c = true.
Proof.
  intros a b c LL LR.
  apply ble_nat_to_le in LL; apply ble_nat_to_le in LR; apply le_trans with (a:=a) (b:=b) (c:=c) in LL.
  apply le_to_ble_nat; apply LL.
  apply LR.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
  | init : R 0 0 0
  | l    : forall m n o, R m n o -> R (S m)    n  (S o)
  | r    : forall m n o, R m n o -> R    m  (S n) (S o).

Theorem R_to_plus :
  forall l r s, R l r s -> l + r = s.
Proof.
  intros l r s.
  generalize dependent l.
  generalize dependent r.
  induction s.
    intros l r R; inversion R; reflexivity.
    intros l r R. inversion R.
      apply IHs in H2; simpl; rewrite H2; reflexivity.
      apply IHs in H2; rewrite plus_comm; rewrite plus_comm in H2; simpl; rewrite H2; reflexivity.
Qed.

Theorem plus_to_R :
  forall l r s, l + r = s -> R l r s.
Proof.
  intros l r s.
  generalize dependent l.
  generalize dependent r.
  induction s.
    intros l r S. destruct l; destruct r. apply init. discriminate. discriminate. discriminate.
    intros l r S. destruct l; destruct r.
      discriminate.
(* TODO *) admit. admit. admit.
Qed.

Require Export Coq.Program.Basics.

Check @compose.

Inductive Contrary {A B} : (A -> B) -> (B -> A) -> Prop :=
(* just test *)
.

Inductive Id {A} : (A -> A) -> Prop :=
  | identity    : Id id
  | composition : forall (B : Type) (f : B -> A) (g : A -> B), Contrary f g -> Id (compose f g).

Definition combine_odd_even (Podd Peven : nat -> Prop) (n : nat) : Prop :=
  (fix combine_odd_even' (Podd Peven : nat -> Prop) (n curr : nat) : Prop :=
    match curr with
    | O => Peven n
    | S O => Podd n
    | S (S curr') => combine_odd_even' Podd Peven n curr'
    end) Podd Peven n n.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (evenb n')
  end.

Fixpoint oddb (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (oddb n')
  end.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat), (oddb n = true -> Podd n) -> (evenb n = true -> Peven n) -> combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n O E.
  unfold combine_odd_even.
  induction n.
    simpl; apply E; reflexivity.
(* TODO this and exercises after this *) admit.
Qed.
