(* definition of walk with an ad hoc predicate
   see:
     Section 15.4 of Coq'Art
     http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/filliatre.pdf
   see also:
     http://www.irisa.fr/celtique/pichardie/papers/genfixpoint.pdf
     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.105.8750
*)

Parameter A : Type.

Inductive term :=
| var : nat -> term
| obj : A -> term
| pair : term -> term -> term
.

Parameter bindings : Type.

Parameter lookup : nat -> bindings -> option term.

Section walk.

Variable s : bindings.

Inductive walk_domain : term -> Prop :=
| walk_domain_1 x : walk_domain (obj x)
| walk_domain_2 x y : walk_domain (pair x y)
| walk_domain_3 v : lookup v s = None -> walk_domain (var v)
| walk_domain_4 v pr : walk_domain pr -> lookup v s = Some pr
    -> walk_domain (var v)
.

Theorem walk_domain_inv :
  forall x v pr, walk_domain x -> x = var v -> lookup v s = Some pr ->
                 walk_domain pr.
Proof.
intros x v pr H.
case H; intros.
discriminate H0.
discriminate H0.
injection H1.
intros.
rewrite H3 in H0.
rewrite H2 in H0.
discriminate H0.
injection H2.
intros.
rewrite H4 in H1.
rewrite H3 in H1.
injection H1.
intros.
rewrite H5.
assumption.
Defined.

Fixpoint walk x (h: walk_domain x) { struct h } : term:=
match x as y return x = y -> term with
| obj _ => fun h' => x
| pair _ _ => fun h' => x
| var v => fun h' =>
  match lookup v s as q return lookup v s = q -> term with
  | None => fun z => x
  | Some pr => fun z => walk pr (walk_domain_inv x v pr h h' z)
  end (refl_equal (lookup v s))
end (refl_equal x).

End walk.

Extraction walk.
