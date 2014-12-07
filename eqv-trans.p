 fof(def_eqv,axiom,(![X,Y]: (eqv(X,Y) <=> (![Z]: (in(Z,X) <=> in(Z,Y)))))).
 fof(trans,conjecture,(![X,Y,Z]: ((eqv(X,Y) & eqv(Y,Z)) => eqv(X,Z)))).