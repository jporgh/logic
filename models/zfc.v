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

Lemma div2_ind :
 forall P : nat -> Prop,
 P O -> (forall n, P (div2 n) -> P n) -> forall n, P n.
Proof.
intros P HO HI n.
apply nat_ind2; intros.
trivial.
apply HI.
simpl.
trivial.
Qed.

Lemma null_extensional : forall m, (forall x, elem x m = false)
 -> m = O.
Proof.
intros m H.
generalize (H O); intros HO.
simpl in HO.
apply odd_div_eq.
simpl.
trivial.
induction m.
trivial.
simpl.
Qed.

Lemma extensionality : forall m n, (forall x, elem x m = elem x n)
 -> m = n.
Proof.
induction m.
induction n.
trivial.
intros.
induction n;intros.
trivial.
double induction m n; intros.
trivial.
generalize (H0 O); intros HO.
simpl in HO.
trivial.
assert (forall y, elem (S y) m = elem (S y) n) as HS.
intros.
rewrite (H (S y)).
trivial.
simpl in HS.
Qed.

End Model.
