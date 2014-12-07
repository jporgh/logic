fof(axiom_t,axiom,(![X,Y,Z]: (eqv(X,Y) => (in(X,Z) <=> in(Y,Z))))).
fof(eqvincompat_left,conjecture,(![X,Y,Z]: ((eqv(X,Y) & in(X,Z)) => in(Y,Z)))).
