fof(def_eqv,axiom,(![X,Y]: (eqv(X,Y) <=> (![Z]: (in(Z,X) <=> in(Z,Y)))))).
fof(refl,conjecture,(![X]: eqv(X,X))).