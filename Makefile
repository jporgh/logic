all: $(patsubst %.p,%.out,$(wildcard *.p))

eqv-axioms.out: eqv-axioms.in
	mace4 -f $< >$@
	
clean:
	rm -f *.in *.out
	
%.in: %.p
	tptp_to_ladr < $< > $@

%.out: %.in
	prover9 -f $< > $@