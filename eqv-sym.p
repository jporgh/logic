fof(def_eqv,axiom,(![X,Y]: (eqv(X,Y) <=> (![Z]: (in(Z,X) <=> in(Z,Y)))))).
fof(sym,conjecture,(![X,Y]: (eqv(X,Y) => eqv(Y,X)))).