Theorem plus_n_n_injective :
  forall n m : nat, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n; induction m.
    reflexivity.
    discriminate.
    discriminate.
    assert (T : forall a b : nat, S (a + b) = a + S b).
      induction a.
        reflexivity.
        simpl. intro b. rewrite IHa. reflexivity.
    intro eq. simpl in eq. rewrite <- T in eq. rewrite <- T in eq. inversion eq.
    apply IHn in H0.
    rewrite H0.
    reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective :
  forall n m : nat, double n = double m -> n = m.
Proof.
  intros n.
  induction n.
    intros m.
    induction m.
      reflexivity.
      discriminate.
    induction m.
      discriminate.
      intros eq.
      simpl in eq.
      inversion eq.
      apply IHn in H0.
      rewrite H0.
      reflexivity.
Qed.

Fixpoint combine {X Y} (xs : list X) (ys : list Y) : list (X * Y) :=
  match (xs,ys) with
  | (nil,_) => nil
  | (_,nil) => nil
  | (cons x xs', cons y ys') => cons (x,y) (combine xs' ys')
  end.

Fixpoint map {X Y} (f : X -> Y) (xs : list X) : list Y :=
  match xs with
  | nil => nil
  | cons x xs' => cons (f x) (map f xs')
  end.

Definition split {X Y} (xys : list (X * Y)) : list X * list Y :=
  (map (fun p => match p with (x,_) => x end) xys,
   map (fun p => match p with (_,y) => y end) xys).

Theorem combine_split {X Y} :
  forall (l : list (X * Y)) l1 l2, split l = (l1,l2) -> combine l1 l2 = l.
Proof.
  intros l.
    induction l.
      intros. simpl in H. inversion H. reflexivity.
      intros. destruct a. simpl in H. inversion H. simpl. rewrite IHl. reflexivity.
      unfold split. reflexivity.
Qed.

Theorem bool_fn_thrice :
  forall (f : bool -> bool) (x : bool), f (f (f x)) = f x.
Proof.
  intros f x.
  destruct (f true) as [] _eqn:T;
    destruct (f false) as [] _eqn:F;
      destruct x.
        rewrite 3 T; reflexivity.
        rewrite F; rewrite 2 T; reflexivity.
        rewrite 3 T; reflexivity.
        rewrite 3 F; reflexivity.
        rewrite T; rewrite F; rewrite T; reflexivity.
        rewrite F; rewrite T; rewrite F; reflexivity.
        rewrite T; rewrite F; rewrite F; reflexivity.
        rewrite 3 F; reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match (n,m) with
  | (O,O) => true
  | (S n', S m') => beq_nat n' m'
  | _ => false
  end.

Theorem beq_nat_sym :
  forall n m, beq_nat n m = beq_nat m n.
Proof.
  intro n.
  induction n.
    intro m; induction m.
      reflexivity.
      reflexivity.
    intro m; induction m.
      reflexivity.
      simpl; apply IHn.
Qed.

Theorem split_combine {X Y} :
  forall (l : list (X * Y)) l1 l2, length l1 = length l2 -> combine l1 l2 = l -> split l = (l1,l2).
Proof.
  intros.
  generalize dependent l.
  generalize dependent l2.
  induction l1.
    destruct l2.
      intros; simpl in H0; rewrite <- H0; compute; reflexivity.
      intros; discriminate.
    destruct l2.
      intros; discriminate.
      intros; simpl in H; simpl in H0; inversion H. destruct l.
        discriminate.
        inversion H0; rewrite H4; apply IHl1 in H4.
        unfold split; unfold split in H4; simpl; simpl in H4; inversion H4.
        rewrite H5; rewrite H6; reflexivity.
        inversion H; reflexivity.
Qed.

Fixpoint filter {X} (p : X -> bool) (xs : list X) : list X :=
  match xs with
  | nil => nil
  | cons x xs' => if p x
                  then cons x (filter p xs')
                  else (filter p xs')
  end.

Theorem filter_exercise {X} :
  forall (p : X -> bool) (x : X) (xs xs' : list X), filter p xs = cons x xs' -> p x = true.
Proof.
  intros.
  generalize dependent x.
  generalize dependent xs'.
  induction xs.
    discriminate.
    intros. destruct (p a) as [] _eqn:P.
      simpl in H; rewrite P in H; inversion H; rewrite H1 in P; apply P.
      simpl in H; rewrite P in H; apply IHxs with xs'; apply H.
Qed.