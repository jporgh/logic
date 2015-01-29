(* hailstone sequences *)

Require Import Div2.
Require Import Even.
Require Import Peano_dec.

Definition hailstoneStep (n : nat) : nat :=
if even_odd_dec n
then div2 n
else 3 * n + 1.

(* hailstone sequence for n *)
Fixpoint hailstone (n : nat) (m : nat) {struct m} : nat :=
match m with
| O => n
| S m => hailstone (hailstoneStep n) m
end.

Inductive hailstone1Rel : nat -> nat -> Prop :=
| hailstone1Rel_1 :
    hailstone1Rel 1 0
| hailstone1Rel_2 n x :
    n <> 1 ->
    hailstone1Rel (hailstoneStep n) x ->
    hailstone1Rel n (S x)
.

Lemma hailston1Rel_correct: forall n y,
  hailstone1Rel n y ->
  hailstone n y = 1.
Proof.
intros n y H.
generalize dependent n.
induction y; intros.
simpl.
inversion H.
trivial.
simpl.
apply IHy.
inversion H.
trivial.
Qed.

Lemma hailstone1Rel_deterministic: forall n y1 y2,
  hailstone1Rel n y1 ->
  hailstone1Rel n y2 ->
  y1 = y2.
Proof.
intros n y1 y2 H1 H2.
generalize dependent y2.
induction H1; inversion 1; auto; congruence.
Qed.

Lemma hailstone1Rel_decidable: forall x y,
  { hailstone1Rel x y }+{ ~ hailstone1Rel x y }.
Proof.
intros.
generalize dependent x.
induction y; intros.
destruct (eq_nat_dec x 1).
left.
subst.
constructor.
right.
intro H.
inversion H.
auto.

destruct (eq_nat_dec x 1).
right.
subst.
intro H.
inversion H.
auto.
destruct (IHy (hailstoneStep x)).
left.
constructor.
trivial.
trivial.
right.
intro H.
inversion H.
tauto.
Qed.

Lemma hailstone1Rel_0: forall y,
  ~ hailstone1Rel 0 y.
Proof.
inversion 1.
subst.
unfold hailstoneStep in *.
simpl in *.
apply hailstone1Rel_deterministic with (y1:=x) in H.
apply n_Sn in H.
trivial.
assumption.
Qed.

Inductive hailstone1Dom : nat -> Prop :=
| hailstone1Dom_1 :
    hailstone1Dom 1
| hailstone1Dom_2 n :
    n <> 1 ->
    hailstone1Dom (hailstoneStep n) ->
    hailstone1Dom n
.

Lemma hailstone1Dom_inv1 :
  forall n,
  hailstone1Dom n ->
  n <> 1 ->
  hailstone1Dom (hailstoneStep n).
Proof.
intros n h.
case h; intros.
congruence.
assumption.
Defined.

(* return position of 1 in hailstone sequence for n *)
Fixpoint hailstone1 (n : nat)
                    (h : hailstone1Dom n) {struct h} :
                    { y | hailstone1Rel n y }.
refine (
  if eq_nat_dec n 1
  then exist _ 0 _
  else exist _ (S (proj1_sig (hailstone1 (hailstoneStep n) (hailstone1Dom_inv1 n h _)))) _
).
subst.
constructor.
match goal with
| |- context [proj1_sig ?X] => destruct X; simpl
end.
constructor; assumption.
Grab Existential Variables.
assumption.
Defined.

Fixpoint hailstone1Iter (n : nat)
                        (z : nat) {struct z} :
                        { y | hailstone1Rel n y }
                        +{ m | forall y, hailstone1Rel m y ->
                               hailstone1Rel n (z + y) }.
refine (
  match z with
  | O => inr _ (exist _ n _)
  | S z => if eq_nat_dec n 1
           then inl _ (exist _ 0 _)
           else match hailstone1Iter (hailstoneStep n) z with
                | inl (exist y _) => inl _ (exist _ (S y) _)
                | inr (exist m _) => inr _ (exist _ m _)
                end
  end
).
trivial.
subst.
constructor.
constructor.
trivial.
trivial.
intros.
simpl.
constructor.
trivial.
auto.
Defined.

Example ex1: hailstone1Rel 6 8.
Proof.
remember (hailstone1Iter 6 10) as s.
compute in Heqs.
destruct s; try congruence.
destruct s.
injection Heqs.
intros.
subst.
trivial.
Qed.
