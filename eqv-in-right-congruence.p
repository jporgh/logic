fof(def_eqv,axiom,(![X,Y]: (eqv(X,Y) <=> (![Z]: (in(Z,X) <=> in(Z,Y)))))).
fof(eqvincomapt_right,conjecture,(![X,Y,Z]: ((eqv(X,Y) & in(Z,X)) => in(Z,Y)))).