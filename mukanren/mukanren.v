Require Import Peano_dec.

Section MuKanren.

Variable A : Type.

Inductive term :=
| var : nat -> term
| obj : A -> term
| pair : term -> term -> term
.

Inductive binding :=
| bind : nat -> term -> binding.

Fixpoint lookup u s :=
match s with
| nil => None
| cons (bind v x) t => if eq_nat_dec u v
                       then Some x
                       else lookup u t
end.

Inductive ground : term -> Prop :=
| gObj x : ground (obj x)
| gPair x y : ground x -> ground y -> ground (pair x y)
.

Section walk.

Variable s : list binding.

Inductive walk : term -> term -> Prop :=
| walkRec v pr t :
    lookup v s = Some pr -> walk pr t -> walk (var v) t
| walkVar v :
    lookup v s = None -> walk (var v) (var v)
| walkObj x :
    walk (obj x) (obj x)
| walkPair t1 t2 :
    walk (pair t1 t2) (pair t1 t2)
.

Lemma walk_ground: forall u,
 ground u -> walk u u.
Proof.
intros u H.
inversion_clear H.
constructor.
constructor.
Qed.

Lemma walk_idempotent: forall u v,
  walk u v -> walk v v.
Proof.
intros u v H.
induction H.
trivial.
constructor.
trivial.
constructor.
constructor.
Qed.

Lemma none_not_some : forall T (x : option T) (y : T),
  x = Some y -> x = None -> False.
Proof.
intros T x y H1 H2.
rewrite H1 in H2.
discriminate H2.
Qed.

Lemma walk_eq: forall u v w,
  walk u v -> walk v w -> v = w.
Proof.
cut (forall u v, walk u v -> forall w, walk v w -> v = w); [eauto|].
intros u v H.
induction H; intros w Hw.
auto.
inversion Hw.
elimtype False.
eauto using none_not_some.
trivial.
inversion Hw.
trivial.
inversion Hw.
trivial.
Qed.

Lemma walk_trans: forall u v w,
  walk u v -> walk v w -> walk u w.
Proof.
intros u v w Hu Hv.
apply (walk_eq u) in Hv.
subst.
trivial.
trivial.
Qed.

Lemma some_injective : forall T (x : option T) (y z : T),
  x = Some y -> x = Some z -> y = z.
Proof.
intros T x y z Hy Hz.
rewrite Hy in Hz.
injection Hz.
trivial.
Qed.

Lemma walk_deterministic: forall v t1 t2,
  walk v t1 -> walk v t2 -> t1 = t2.
Proof.
cut (forall v t1 : term, walk v t1 -> forall t2 : term, walk v t2 -> t1 = t2); [eauto|].
intros v t1 H1.
induction H1; intros w Hw.
apply IHwalk.
inversion_clear Hw.
match goal with
| H : _ = Some _ |- _ => eapply some_injective in H; [|clear H; eassumption]
end.
subst.
trivial.
elimtype False.
eauto using none_not_some.
inversion_clear Hw.
elimtype False.
eauto using none_not_some.
trivial.
inversion_clear Hw.
trivial.
inversion_clear Hw.
trivial.
Qed.

End walk.

Section occurs.

Variable s : list binding.
Variable x : nat.

Inductive occurs : term -> Prop :=
| occursVar v :
   walk s v (var x) -> occurs v
| occursLeft v v1 v2:
   walk s v (pair v1 v2) -> occurs v1 -> occurs v
| occursRight v v1 v2:
   walk s v (pair v1 v2) -> occurs v2 -> occurs v
.

Lemma not_occurs_var: forall n v,
  walk s v (var n) ->
  ~ occurs (var n) -> n <> x.
Proof.
intros n v Hw Ho Hne.
subst.
destruct Ho.
constructor.
eapply walk_idempotent.
eauto.
Qed.

End occurs.

Definition ext_s x v s := cons (bind x v) s.

Lemma ext_new_var : forall x n s y q,
y <> var n ->
lookup n s = None ->
walk s x y ->
walk (ext_s n q s) x y.
Proof.
intros x n s y q Ho Hl Hw.
generalize dependent n.
generalize dependent q.
induction Hw; intros.
apply walkRec with (pr := pr).
simpl.
destruct eq_nat_dec.
subst.
elimtype False.
eauto using none_not_some.
trivial.
apply IHHw.
trivial.
trivial.
apply walkVar.
simpl.
destruct eq_nat_dec.
subst.
tauto.
trivial.
constructor.
constructor.
Qed.

Definition non_circular s :=
 forall t, exists u, walk s t u.

Lemma non_circular_weak : forall s,
 ( forall n x, lookup n s = Some x -> exists u, walk s (var n) u ) ->
 non_circular s.
Proof.
intros s H.
red;intros.
destruct t.
destruct (lookup n s) eqn:?.
destruct (H n t).
trivial.
exists x.
trivial.
exists (var n).
constructor.
trivial.
exists (obj a).
constructor.
exists (pair t1 t2).
constructor.
Qed.

Definition bad_ext v w s :=
  walk s (var w) (var v).

Lemma bad_occurs : forall v w s,
  ~ occurs s v (var w) ->
  ~ bad_ext v w s.
Proof.
intros v w s H1 H2.
destruct H1.
red in H2.
constructor.
trivial.
Qed.

Lemma walk_lookup : forall s t n,
  walk s t (var n) ->
  lookup n s = None.
Proof.
intros s t n H.
remember (var n) as u.
induction H.
tauto.
injection Hequ.
intros; subst.
trivial.
discriminate Hequ.
discriminate Hequ.
Qed.

Lemma walk_ext : forall s t x v w,
 walk s t (var x) ->
 walk s v w ->
 w <> var x ->
 walk (ext_s x v s) t w.
Proof.
intros s t x v w Ht Hv Hne.
generalize dependent w.
generalize dependent v.
remember (var x) as u.
induction Ht; intros.
subst.
lapply IHHt; clear IHHt; trivial; intros.
assert (v <> x).
red; intros; subst.
apply walk_lookup in Ht.
rewrite Ht in H.
discriminate H.
apply walkRec with (pr := pr).
simpl.
destruct eq_nat_dec.
tauto.
trivial.
apply H0.
trivial.
trivial.
injection Hequ.
clear Hequ; intros; subst.
apply walkRec with (pr := v0).
simpl.
destruct eq_nat_dec.
trivial.
tauto.
apply ext_new_var.
trivial.
trivial.
trivial.
discriminate Hequ.
discriminate Hequ.
Qed.

Lemma prevent_bad_circularities : forall s x w,
  non_circular s ->
  lookup x s = None ->
  ~ bad_ext x w s ->
  non_circular (ext_s x (var w) s).
Proof.
intros s x w Hcirc Hlook Hbad.
apply non_circular_weak.
intros n u H.
unfold bad_ext in Hbad.

unfold non_circular in Hcirc.
destruct (Hcirc (var n)).

destruct x0.
destruct (eq_nat_dec n0 x).
subst.
destruct (Hcirc (var w)).
exists x0.
apply walk_ext.
trivial.
trivial.
red;intros; subst.
tauto.

exists (var n0).
apply ext_new_var.
red;intros; destruct n1; subst.
injection H1.
trivial.
trivial.
trivial.

exists (obj a).
apply ext_new_var.
discriminate 1.
trivial.
trivial.

exists (pair x0_1 x0_2).
apply ext_new_var.
discriminate 1.
trivial.
trivial.
Qed.

Definition dec_term_var t : { n | t = var n }+{ forall n, t <> var n }.
Proof.
destruct t.
left.
exists n.
trivial.
right.
discriminate 1.
right.
discriminate 1.
Defined.

Definition dec_term_varn t n : { t = var n }+{ t <> var n }.
Proof.
destruct (dec_term_var t).
destruct s.
destruct (eq_nat_dec n x).
subst.
tauto.
right.
subst.
injection 1.
auto.
right.
trivial.
Defined.
 
Lemma prevent_circularities : forall s x v,
  non_circular s ->
  lookup x s = None ->
  ~ occurs s x v ->
  non_circular (ext_s x v s).
Proof.
intros s x v Hcirc Hlook Hocc.
destruct (dec_term_var v).
destruct s0.
subst.
apply prevent_bad_circularities.
trivial.
trivial.
apply bad_occurs.
trivial.

clear Hocc.
red; intros.
unfold non_circular in Hcirc.
destruct (Hcirc t).

destruct (dec_term_varn x0 x).

subst.
exists v.
apply walk_ext.
trivial.
destruct v.
destruct (n n0).
trivial.
constructor.
constructor.
trivial.

exists x0.
apply ext_new_var.
trivial.
trivial.
trivial.
Qed.

Inductive unify : term -> term -> list binding -> list binding -> Prop :=
| unifyVars u v s w :
    walk s u (var w) -> walk s v (var w) -> unify u v s s
| unifyVarPair u v s w p1 p2 :
    walk s u (var w) -> walk s v (pair p1 p2) -> unify u v s (ext_s w v s)
| unifyVarObj u v s w x :
    walk s u (var w) -> walk s v (obj x) -> unify u v s (ext_s w v s)
| unifyPairVar u v s w p1 p2 :
    walk s u (pair p1 p2) -> walk s v (var w) -> unify u v s (ext_s w u s)
| unifyObjVar u v s w x :
    walk s u (obj x) -> walk s v (var w) -> unify u v s (ext_s w u s)
| unifyPairs u v s u1 u2 v1 v2 s1 s2:
    walk s u (pair u1 u2) -> walk s v (pair v1 v2) ->
    unify u1 v1 s s1 -> unify u2 v2 s1 s2 -> unify u v s s2
| unifyObjs u v s x :
    walk s u (obj x) -> walk s v (obj x) -> unify u v s s
.

Lemma unify_ground : forall x s, ground x -> unify x x s s.
Proof.
intros x s H.
assert (Hw: walk s x x) by auto using walk_ground.
induction H.
eapply unifyObjs.
eassumption.
trivial.
eapply unifyPairs.
eassumption.
eassumption.
eauto using walk_ground.
auto using walk_ground.
Qed.

End MuKanren.
