(* extracting an infinite loop *)

Fixpoint loop (x : nat) (h : False) {struct h} : nat :=
  loop (S x) (False_ind _ h).

Extraction loop.
