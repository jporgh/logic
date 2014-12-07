fof(def_eqv,axiom,(![X,Y]: (eqv(X,Y) <=> (![Z]: (in(Z,X) <=> in(Z,Y)))))).
fof(axiom_t,axiom,(![X,Y,Z]: (eqv(X,Y) => (in(X,Z) <=> in(Y,Z))))).