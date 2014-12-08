fof(class_equality,axiom,(![X,Y]: ((![Z]: (in(Z,X) <=> in(Z,Y))) => X=Y))).
fof(def_set,axiom,(![X]: (set(X) <=> (?[Y]: in(X,Y))))).
fof(null_unique,conjecture,
  (![X1]: (set(X1) => ((![Y]: (set(Y) => ~in(Y,X1))) =>
  (![X2]: (set(X2) => ((![Y]: (set(Y) => ~in(Y,X2))) =>
  X1=X2))))))).