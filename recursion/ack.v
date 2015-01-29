(* Ackermann function *)

Inductive ackRel : nat -> nat -> nat -> Prop :=
| ackRel_1 n : 
    ackRel 0 n (n + 1)
| ackRel_2 m1 x :
    ackRel m1 1 x ->
    ackRel (S m1) 0 x
| ackRel_3 m1 n1 x x0 :
    ackRel (S m1) n1 x0 ->
    ackRel m1 x0 x ->
    ackRel (S m1) (S n1) x
.

Lemma ackRel_deterministic : forall r x x0 x1,
  ackRel x0 x1 r ->
  ackRel x0 x1 x ->
  r = x.
Proof.
intros.
match goal with
| H: ackRel _ _ ?X |- _ => generalize dependent X
end.
match goal with
| H: ackRel _ _ _ |- _ => induction H
end.
{
  inversion 1.
  reflexivity.
}
{
  inversion 1.
  subst.
  auto.
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

Inductive ackDom : nat -> nat -> Prop :=
| ackDom_1 n : 
    ackDom 0 n
| ackDom_2 m1 :
    ackDom m1 1 ->
    ackDom (S m1) 0
| ackDom_3 m1 n1 x0 :
    ackDom (S m1) n1 ->
    ackRel (S m1) n1 x0 ->
    ackDom m1 x0 ->
    ackDom (S m1) (S n1)
.

Lemma ackDom_inv1 :
 forall m n,
 ackDom m n ->
 forall m1,
  m = S m1 ->
  n = 0 ->
 ackDom m1 1.
Proof.
intros m n h.
case h; intros.
discriminate H.
injection H0.
intros; subst.
assumption.
discriminate H3.
Defined.

Lemma ackDom_inv2 :
  forall m n,
  ackDom m n ->
  forall m1 n1,
  m = S m1 ->
  n = S n1 ->
  ackDom (S m1) n1.
Proof.
intros m n h.
case h; intros.
discriminate H.
discriminate H1.
injection H2.
injection H3.
intros; subst.
assumption.
Defined.

Lemma ackDom_inv3 :
  forall m n,
  ackDom m n ->
  forall m1 n1,
  m = S m1 ->
  n = S n1 ->
  forall s: { y | ackRel (S m1) n1 y },
  ackDom m1 (proj1_sig s).
Proof.
intros m n h.
case h; intros.
discriminate H.
discriminate H1.
injection H2.
injection H3.
intros; subst.
destruct s.
simpl.
replace x with x0.
assumption.
eapply ackRel_deterministic.
eassumption.
assumption.
Defined.

Fixpoint ack (m n : nat) 
             (h : ackDom m n) {struct h} :
             { y | ackRel m n y }.
refine (
  match m as m' return m = m' -> _ with
  | O => fun Hm => exist _ (n + 1) _
  | S m1 => fun Hm => match n as n' return n = n' -> _ with
            | O => fun Hn => exist _ (proj1_sig (ack m1 1 (ackDom_inv1 m n h m1 Hm Hn))) _
            | S n1 => fun Hn => exist _ (proj1_sig (ack m1 (proj1_sig (ack (S m1) n1 (ackDom_inv2 m n h m1 n1 Hm Hn))) (ackDom_inv3 m n h m1 n1 Hm Hn _))) _
            end (refl_equal _)
  end (refl_equal _)
);
repeat match goal with
| H: context [proj1_sig ?X] |- _ => destruct X; simpl in H
| |- context [proj1_sig ?X] => destruct X; simpl
end;
try (subst; econstructor; eassumption).
Defined.

Lemma ackDom_total : forall m n,
  ackDom m n.
Proof.
induction m as [|m IHm]; intros n.
{
  constructor.
}
{
  induction n as [|n IHn].
  {
    constructor.
    apply IHm. 
  }
  {
    destruct (ack (S m) n IHn) as [x H].
    econstructor.
    assumption.  
    eassumption.
    apply IHm.
  }
}
Qed.