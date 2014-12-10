Require Import Bool.

Section Model.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint oddb (n : nat) : bool :=
match n with
| O => false
| S n => negb (oddb n)
end.

Fixpoint div2 (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S n) => S (div2 n)
end.

Fixpoint elem (n m : nat) {struct n}: bool :=
match n with
| O => oddb m
| S n => elem n (div2 m)
end.

Lemma O_is_emptyset : forall n, elem n O = false.
Proof.
induction n; auto.
Qed.

Lemma odd_div_eq : 
   forall m n : nat, oddb m = oddb n -> div2 m = div2 n -> m = n.
Proof.
Qed.

Lemma extensionality : forall m n, (forall x, elem x m = elem x n)
 -> m = n.
Proof.
intros m n H.
induction n.
destruct m.
trivial.
Qed.

End Model.
