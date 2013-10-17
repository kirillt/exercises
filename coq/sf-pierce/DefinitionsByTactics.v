(* Short example. *)

Definition length' : natlist -> nat.
intro lst.
induction lst as [ | h t ].
  exact 0.
  exact (1 + IHt).
Defined.

Extraction Language Haskell.

Extraction "test.hs" length'.
