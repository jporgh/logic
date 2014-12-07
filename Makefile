.p.in:
    tptp2ladr < $< > $@

.in.out:
    prover9 -f $< > $@