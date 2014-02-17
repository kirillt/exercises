Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(* Source language *)

Inductive binop : Set := Plus | Mult.
Inductive exp : Set :=
  | Const : nat -> exp
  | Binop : exp -> binop -> exp -> exp.

Definition binopDenote (l : nat) (o : binop) (r : nat) : nat :=
  match o with
  | Plus => l + r
  | Mult => l * r
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const x => x
  | Binop l o r => binopDenote (expDenote l) o (expDenote r)
  end.

(* Target language *)

Inductive instr : Set :=
  | iConst : nat -> instr
  | iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst x => Some (x :: s)
  | iBinop o =>
    match s with
    | l :: r :: s' => Some ((binopDenote l o r) :: s')
    | _ => None
    end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | i :: p' =>
    match instrDenote i s with
    | Some s' => progDenote p' s'
    | None => None
    end
  | _ => Some s
  end.

(* Translation *)

Fixpoint compile (e : exp) : prog:=
  match e with
  | Const x => iConst x :: nil
  | Binop l o r => compile r ++ compile l ++ iBinop o :: nil
  end.

Lemma compile_correct' e : forall p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e; [ intros | intros; simpl;
    rewrite app_assoc_reverse; rewrite IHe2;
    rewrite app_assoc_reverse; rewrite IHe1 ];
    reflexivity.
Qed.

Theorem compile_correct e : progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intros;
  rewrite (app_nil_end (compile e));
  rewrite compile_correct';
  reflexivity.
Qed.

(* *** Typed *** *)

(* Source language *)

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
  | TPlus : tbinop Nat Nat Nat
  | TMult : tbinop Nat Nat Nat
  | TEq   : forall t, tbinop t t Bool
  | TLt   : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
  | TNConst : nat  -> texp Nat
  | TBConst : bool -> texp Bool
  | TBinop  : forall x y z, tbinop x y z -> texp x -> texp y -> texp z.

Definition typeDenote t : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Definition tbinopDenote x y z (o : tbinop x y z) : typeDenote x -> typeDenote y -> typeDenote z :=
  match o with
  | TPlus    => plus
  | TMult    => mult
  | TEq Nat  => beq_nat
  | TEq Bool => eqb
  | TLt      => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ o l r => tbinopDenote o (texpDenote l) (texpDenote r)
  end.

(* Target language *)

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
  | TNiConst : forall s, nat  -> tinstr s (Nat  :: s)
  | TBiConst : forall s, bool -> tinstr s (Bool :: s)
  | TiBinop   : forall s x y z, tbinop x y z ->
                 tinstr (x :: y :: s) (z :: s).

Inductive tprog : tstack -> tstack -> Set :=
  | TNil  : forall s, tprog s s
  | TCons : forall s1 s2 s3, tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | cons t ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TNiConst _ n => fun s => (n, s)
  | TBiConst _ b => fun s => (b, s)
  | TiBinop  _ _ _ _ o => fun s =>
    let '(x,(y,s')) := s in (tbinopDenote o x y, s')
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
  | TNil _ => fun s => s
  | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(* Translation *)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
  | TNil _ => fun p' => p'
  | TCons _ _ _ i p' => fun p'' => TCons i (tconcat p' p'')
  end.

Fixpoint tcompile t (e : texp t) ts : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TNiConst _ n) (TNil _)
  | TBConst b => TCons (TBiConst _ b) (TNil _)
  | TBinop _ _ _ o x y => tconcat (tcompile y _) (tconcat (tcompile x _) (TCons (TiBinop _ o) (TNil _)))
  end.