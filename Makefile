all: $(patsubst %.p,%.out,$(wildcard *.p))

clean:
	rm -f *.in *.out
	
%.in: %.p
	tptp_to_ladr < $< > $@

%.out: %.in
	prover9 -f $< > $@