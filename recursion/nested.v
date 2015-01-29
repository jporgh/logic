* definition of a function with nested recursion using an ad hoc predicate
   see:
     Chapter 15 (General Recursion) of Coq'Art
*)

Require Import Div2.
Require Import Omega.

Inductive nestedRel : nat -> nat -> Prop :=
| nestedRel_1 :
    nestedRel 0 0
| nestedRel_2 x r s :
    nestedRel (div2 x) r ->
    nestedRel ((div2 x) + r) s ->
    nestedRel (S x) (1 + s)
.

Lemma nestedRel_deterministic : forall r x x0,
  nestedRel x0 r ->
  nestedRel x0 x ->
  r = x.
Proof.
intros.
match goal with
| H: nestedRel _ ?X |- _ => generalize dependent X
end.
match goal with
| H: nestedRel _ _ |- _ => induction H
end.
{
  inversion 1.
  reflexivity.
}
{
  inversion 1.
  subst.
  repeat match goal with
  | H: forall x, _ -> _ |- _ =>
    match goal with
    | K: _ |- _ => apply H in K; rewrite K in *; clear K
    end
  end.
  reflexivity.
}
Qed.

Inductive nestedDom : nat -> Prop :=
| nestedDom_1 :
    nestedDom 0
| nestedDom_2 x r :
    nestedDom (div2 x) ->
    nestedRel (div2 x) r ->
    nestedDom (div2 x + r) ->
    nestedDom (S x)
.

Hint Constructors nestedDom.

Lemma nestedDom_complete : forall x y,
  nestedRel x y ->
  nestedDom x.
Proof.
intros x y H.
induction H; eauto.
Qed.

Lemma nestedDom_inv1 : forall x : nat,
  nestedDom x ->
  forall p : nat, x = S p -> nestedDom (div2 p).
Proof.
intros x h.
case h; try (discriminate 1).
intros.
match goal with
| H: S ?X = S _ |- _ => injection H; clear H; intros; subst X
end.
assumption.
Defined.

Lemma nestedDom_inv2 :
forall x : nat, nestedDom x ->
forall p : nat, x = S p ->
forall s : {y : nat | nestedRel (div2 p) y},
nestedDom (div2 p + proj1_sig s).
Proof.
intros x h.
case h; try (intros ? H; elimtype False; abstract (discriminate H)).
intros x0 r _ ? ? p ? s.
assert (x0 = p) by abstract auto.
replace (proj1_sig s) with r.
{
  replace p with x0.
  assumption.
}
abstract (
  subst;
  case s;
  eauto using nestedRel_deterministic
).
Defined.

Fixpoint nested (x : nat) (h : nestedDom x) { struct h } :
                { y : nat | nestedRel x y }.
refine (
  match x as x' return x = x' -> _ with
  | O => fun hx => exist _
         O
         _
  | S p => fun hx => exist _
           (1 + proj1_sig
                (nested (div2 p +
                         proj1_sig
                         (nested (div2 p) (nestedDom_inv1 x h p hx)))
                        (nestedDom_inv2 x h p hx _)))
           _
  end (refl_equal _)
).
{
  subst.
  apply nestedRel_1.
}
{
  repeat match goal with
  | [ H: context [proj1_sig ?X] |- _ ] => destruct X; simpl in H
  | |- context [proj1_sig ?X] => destruct X; simpl
  end.
  subst.
  eapply nestedRel_2; eassumption.
}
Defined.

Lemma double_div2_le : forall x,
  div2 x + div2 x <= x.
Proof.
intros x.
pattern x.
match goal with
| |- ?P x => cut (P x /\ P (S x)); [tauto|]
end.
induction x; auto.
split.
{
  tauto.
}
{
  simpl.
  omega.
}
Qed.

Lemma nestedRel_le : forall x y,
  nestedRel x y ->
  y <= x.
Proof.
intros x y H.
induction H; trivial.
pose (double_div2_le x).
omega.
Qed.

Lemma nestedDom_total: forall x,
  nestedDom x.
Proof.
intros x.
cut (forall y, y <= x -> nestedDom y); auto.
induction x; intros y H.
{
  inversion_clear H.
  trivial.
}
{
  inversion_clear H; auto.
  assert (H: nestedDom (div2 x)) by eauto using double_div2_le with arith.
  destruct (nested _ H) as [x0].
  apply nestedDom_2 with (r:=x0); try assumption.
  match goal with H: _ |- _ => apply H; clear H end.
  match goal with H: nestedRel _ _ |- _ => apply nestedRel_le in H end.
  pose (double_div2_le x).
  omega.
}
Qed.
