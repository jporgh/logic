fof(class_equality,axiom,(![X,Y]: ((![Z]: (in(Z,X) <=> in(Z,Y))) => X=Y))).
fof(def_subseteq,axiom,(![X,Y]: (subseteq(X,Y) <=> (![Z]: (in(Z,X) => in(Z,Y)))))).
fof(subseteq_eq,conjecture,(![X,Y]: ((subseteq(X,Y) & subseteq(Y,X)) => X=Y))).