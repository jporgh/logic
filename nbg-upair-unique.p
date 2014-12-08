fof(class_equality,axiom,(![X,Y]: ((![Z]: (in(Z,X) <=> in(Z,Y))) => X=Y))).
fof(def_set,axiom,(![X]: (set(X) <=> (?[Y]: in(X,Y))))).
fof(upair_unique,conjecture,(![X]: (set(X) => (![Y]: (set(Y) => 
  (![Z1]: (set(Z1) => ((![U]: (set(U) => (in(U,Z1) <=> (U=X | U=Y)))) =>
  (![Z2]: (set(Z2) => ((![U]: (set(U) => (in(U,Z2) <=> (U=X | U=Y)))) =>
  Z1 = Z2))))))))))).
