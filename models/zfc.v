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

Fixpoint mul2 (n : nat) : nat :=
match n with
| O => O
| S n => S (S (mul2 n))
end.

Lemma div2_S : forall n, 
 (oddb n = true -> div2 (S n) = S (div2 n))
/\ (oddb n = false -> div2 (S n) = div2 n).
Proof.
induction n;split.
discriminate 1.
trivial.
intros H.
destruct IHn as [IHodd IHeven].
rewrite IHeven.
simpl.
trivial.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
intros H.
destruct IHn as [IHodd IHeven].
rewrite IHodd.
simpl.
trivial.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
Qed.

Lemma mul2_div2 : forall n, 
   (oddb n = false -> mul2 (div2 n) = n)
/\ (oddb n = true -> S (mul2 (div2 n)) = n).
Proof.
induction n; split.
trivial.
discriminate 1.
intros H.
generalize (div2_S n); intros [Hdiv _].
rewrite Hdiv.
simpl.
destruct IHn as [IHeven IHodd].
rewrite IHodd.
trivial.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
intros H.
generalize (div2_S n); intros [_ Hdiv].
rewrite Hdiv.
simpl.
destruct IHn as [IHeven IHodd].
rewrite IHeven.
trivial.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
simpl in H.
rewrite <- (negb_involutive (oddb n)).
rewrite H.
tauto.
Qed.

Lemma odd_div_eq : 
   forall m n : nat, oddb m = oddb n -> div2 m = div2 n -> m = n.
Proof.
intros m n Hodd Hdiv.
case_eq (oddb m); intros H.
rewrite H in Hodd.
generalize (mul2_div2 n); intros [_ Hn].
generalize (mul2_div2 m); intros [_ Hm].
rewrite <- Hn.
rewrite <- Hm.
rewrite Hdiv.
trivial.
trivial.
auto.
rewrite H in Hodd.
generalize (mul2_div2 n); intros [Hn _].
generalize (mul2_div2 m); intros [Hm _].
rewrite <- Hn.
rewrite <- Hm.
rewrite Hdiv.
trivial.
trivial.
auto.
Qed.

Lemma nat_ind2 :
 forall P : nat -> Prop,
 P O -> P (S O) -> (forall n, P n -> P (S (S n))) -> 
forall n, P n.
Proof.
intros P H1 H2 HI n.
assert (P n /\ P (S n)).
induction n; split.
trivial.
trivial.
tauto.
apply HI.
tauto.
tauto.
Qed.

Inductive lt : nat -> nat -> Prop :=
| lt_O : forall n, lt O (S n)
| lt_S : forall m n, lt m n -> lt (S m) (S n).

Lemma lt_S_le : forall m n,
  lt m (S n) ->
  (lt m n \/ m = n).
Proof.
intros m n H.
generalize dependent m.
induction n; intros m H.
right.
inversion_clear H.
trivial.
inversion H0.
inversion_clear H.
left.
apply lt_O.
destruct (IHn m0).
trivial.
left.
apply lt_S.
trivial.
subst.
right.
trivial.
Qed.

Lemma nat_lt_ind :
  forall P : nat -> Prop,
  (forall m, (forall n, lt n m -> P n) -> P m) ->
forall n, P n.
Proof.
intros P HI n.
assert (P n /\ (forall m, lt m n -> P m)).
induction n; split; intros.
apply HI; intros.
inversion H.
inversion H.
destruct IHn.
apply HI; intros.
destruct (lt_S_le n0 n).
trivial.
apply H0.
trivial.
subst.
trivial.
destruct IHn.
destruct (lt_S_le m n).
trivial.
apply H1.
trivial.
subst.
trivial.
tauto.
Qed.

Lemma lt_lt_S : forall m n,
  lt m n ->
  lt m (S n).
Proof.
induction m; intros.
apply lt_O.
apply lt_S.
destruct n.
inversion H.
apply IHm.
inversion_clear H.
trivial.
Qed.

Lemma lt_div2 : forall m,
  lt (div2 (S m)) (S m).
Proof.
  intros m.
  pattern m; apply nat_ind2.
  simpl.
apply lt_O.
simpl.
apply lt_S.
apply lt_O.
intros.
clear m.
replace (div2 (S (S (S n))))
with (S (div2 (S n))).
apply lt_S.
apply lt_lt_S.
trivial.
auto.
Qed.

Lemma div2_ind :
 forall P : nat -> Prop,
 P O -> (forall n, P (div2 n) -> P n) -> forall n, P n.
Proof.
intros P HO HI n.
apply nat_lt_ind; intros.
destruct m.
trivial.
apply HI.
apply H.
apply lt_div2.
Qed.

Lemma null_extensional : forall m, (forall x, elem x m = false)
 -> m = O.
Proof.
refine (div2_ind  _ _ _); intros.
trivial.
assert (n=O \/ n=S O \/ div2 n <> O).
destruct n; auto.
destruct n; auto.
right;right.
simpl.
discriminate.
destruct H1 as [H1 | [ H1 | H1 ]].
auto.
subst.
generalize (H0 O); intros.
simpl in H1.
discriminate H1.
destruct H1.
apply H.
intros.
generalize (H0 (S x)); intros.
simpl in H1.
trivial.
Qed.

Lemma extensionality : forall m n, (forall x, elem x m = elem x n)
 -> m = n.
Proof.
refine (div2_ind _ _ _); intros.
symmetry.
apply null_extensional; intros.
rewrite <- H.
apply O_is_emptyset.
apply odd_div_eq.
generalize (H0 O); simpl; intros.
trivial.
apply H.
intros.
generalize (H0 (S x)); simpl; intros.
trivial.
Qed.

End Model.
