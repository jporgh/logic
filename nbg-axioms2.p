%model
fof(class_equality,axiom,(![X,Y]: ((![Z]: (in(Z,X) <=> in(Z,Y))) => X=Y))).
fof(def_subseteq,axiom,(![X,Y]: (subseteq(X,Y) <=> (![Z]: (in(Z,X) => in(Z,Y)))))).
fof(def_set,axiom,(![X]: (set(X) <=> (?[Y]: in(X,Y))))).
fof(axion_n,axiom,(?[X]: (set(X) & (![Y]: (set(Y) => ~in(Y,X)))))).