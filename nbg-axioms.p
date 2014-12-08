%model
fof(class_equality,axiom,(![X,Y]: ((![Z]: (in(Z,X) <=> in(Z,Y))) => X=Y))).
fof(def_subseteq,axiom,(![X,Y]: (subseteq(X,Y) <=> (![Z]: (in(Z,X) => in(Z,Y)))))).
fof(def_set,axiom,(![X]: (set(X) <=> (?[Y]: in(X,Y))))).
fof(def_empty,axiom,(![Y]: (set(Y) => (~in(Y,empty))))).
fof(def_upair,axiom,(![X,Y]: ((set(X) & set(Y) & (![U]: (in(U,upair(X,Y)) <=> (U=X | U=Y))))
                              | ((~set(X) | ~set(Y)) & upair(X,Y) = empty)))). 
fof(def_sing,axiom,(![X]: (sing(X) = upair(X,X)))).
fof(def_pair,axiom,(![X,Y]: (pair(X,Y) = upair(sing(X), upair(X,Y))))).
fof(def_compl,axiom,(![X,U]: (set(U) => (in(U,compl(X)) <=> ~in(U,X))))).
fof(def_univ,axiom,(univ = compl(empty))).
fof(def_times,axiom,(![Y1,Y2,X]: (set(X) => (in(X,times(Y1,Y2)) <=> (?[U]: (?[V]: (set(U) & set(V) & X=pair(U,V) & U=Y1 & V=Y2))))))). 
fof(def_rel,axiom,(![X]: (rel(X) <=> subseteq(X,times(univ,univ))))).
fof(def_fnc,axiom,(![X]: (fnc(X) <=> (rel(X) & (![W,Y,Z]: ((set(W) & set(Y) & set(Z) & in(pair(W,Y),X) & in(pair(W,Z),X)) => Y=Z)))))). 
fof(axiom_r,axiom,(![Y]: (fnc(Y) => (![X]: (set(X) => (?[R]: (set(R) & (![U]: (set(U) => (in(U,R) <=> (?[V]: (set(V) & in(pair(V,R),Y) & in(V,X))))))))))))).