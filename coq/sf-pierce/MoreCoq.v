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
